import Corpus.CollectCommon
import Corpus.Frontend
import Corpus.Records
import Corpus.SourceSyntax
import Corpus.Verify
import Workers

namespace LeanReassemble

open Lean

structure RewriteConfig where
  sourceRoot : System.FilePath
  records : System.FilePath
  file : String
  output : System.FilePath

structure Edit where
  declaration : String
  range : Lean.Syntax.Range
  replacement : String
  deriving Inhabited, Repr

private structure Candidate where
  name : String
  key : Nat × Nat
  start : Nat × Nat
  deriving Inhabited

private def fail {α} (message : String) : IO α :=
  throw <| IO.userError s!"lean-reassemble: {message}"

private def normalizeRelativePath (path : String) : String :=
  ((path.dropPrefix "./").copy.dropPrefix ".\\").copy

private def isWithin (root path : System.FilePath) : Bool :=
  let root := root.toString
  let path := path.toString
  path == root || path.startsWith (root ++ "/") || path.startsWith (root ++ "\\")

/-- Read and decode one JSON object per nonempty input line. -/
def readRecords (path : System.FilePath) : IO (Array Corpus.ConstRecord) := do
  let input ← IO.FS.readFile path
  let mut records := #[]
  let mut lineNumber := 0
  for line in input.splitOn "\n" do
    lineNumber := lineNumber + 1
    let line := line.trimAscii
    unless line.isEmpty do
      let json ← match Json.parse line.toString with
        | .ok json => pure json
        | .error error => fail s!"malformed JSONL at line {lineNumber}: {error}"
      let record ← match (fromJson? json : Except String Corpus.ConstRecord) with
        | .ok record => pure record
        | .error error => fail s!"invalid record at line {lineNumber}: {error}"
      records := records.push record
  return records

/-- Select theorem records for one source file and reject ambiguous input. -/
def selectTheorems (records : Array Corpus.ConstRecord) (file : String) :
    IO (Array Corpus.ConstRecord) := do
  let requested := normalizeRelativePath file
  let mut selected := #[]
  let mut names : Std.HashSet String := {}
  for record in records do
    if record.kind == "theorem" || record.kind == "private theorem" then
      let some recordFile := record.file
        | fail s!"theorem record {record.name} has no file"
      if normalizeRelativePath recordFile == requested then
        if names.contains record.name then
          fail s!"duplicate theorem record for {record.name}"
        names := names.insert record.name
        selected := selected.push record
  if selected.isEmpty then
    fail s!"no theorem records found for {file}"
  return selected

private def declarationCandidates (frontendResult : Corpus.Frontend.ElabResult) :
    IO (Array Candidate) :=
  Corpus.Frontend.runCollectorOn frontendResult do
    let mut candidates := #[]
    for verified in (← Corpus.Verify.verifiedFileConstants) do
      match verified.info with
      | .thmInfo _ =>
          if let some ranges ← Lean.findDeclarationRanges? verified.info.name then
            candidates := candidates.push {
              name := (Corpus.CollectCommon.displayName verified.info.name).toString
              key := (ranges.selectionRange.pos.line, ranges.selectionRange.pos.column)
              start := (ranges.range.pos.line, ranges.range.pos.column)
            }
      | _ => pure ()
    return candidates

private def commandForKey? (source : String) (commands : Array Syntax)
    (key : Nat × Nat) : Option Syntax :=
  let fileMap := source.toFileMap
  commands.find? fun command =>
    command.getKind == ``Lean.Parser.Command.declaration &&
      Corpus.SourceSyntax.declarationKey? fileMap command == some key

private def commandIndent (source : String) (command : Syntax) : String := Id.run do
  let some range := Corpus.SourceSyntax.commandRange? command | return ""
  let fileMap := source.toFileMap
  let position := fileMap.toPosition range.start
  let lineStart := fileMap.lineStart position.line
  let whitespace := String.Pos.Raw.extract source lineStart range.start
  if whitespace.all fun char => char == ' ' || char == '\t' then whitespace else ""

private def replacementFor (kind : Corpus.SourceSyntax.DeclValueKind)
    (indent : String) : String :=
  let proof := s!"by\n{indent}  sorry"
  match kind with
  | .simple => proof
  | .equations | .whereBody => s!":= {proof}"

/-- Validate edit bounds and reject overlapping source ranges. -/
def validateEdits (source : String) (edits : Array Edit) : IO Unit := do
  let sourceSize := source.rawEndPos.byteIdx
  for edit in edits do
    if edit.range.start.byteIdx > edit.range.stop.byteIdx ||
        edit.range.stop.byteIdx > sourceSize then
      fail s!"invalid proof range for {edit.declaration}"
  let ascending := edits.qsort fun a b => a.range.start.byteIdx < b.range.start.byteIdx
  for index in [1:ascending.size] do
    let previous := ascending[index - 1]!
    let current := ascending[index]!
    if current.range.start.byteIdx < previous.range.stop.byteIdx then
      fail s!"overlapping proof ranges for {previous.declaration} and {current.declaration}"

/-- Match records to declarations and compute non-overlapping source edits. -/
def planEdits (frontendResult : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) : IO (Array Edit) := do
  let candidates ← declarationCandidates frontendResult
  let mut edits := #[]
  let mut matchedKeys : Std.HashSet (Nat × Nat) := {}
  for record in records do
    if record.module != frontendResult.file.module.toString then
      fail s!"record module does not match source file for {record.name}"
    let matchingCandidates := candidates.filter fun candidate =>
      candidate.name == record.name &&
        (record.startLine.map (· == candidate.start.1)).getD true &&
        (record.startCol.map (· == candidate.start.2)).getD true
    if matchingCandidates.size == 0 then
      fail s!"theorem record did not match a declaration: {record.name}"
    if matchingCandidates.size != 1 then
      fail s!"theorem record matched {matchingCandidates.size} declarations: {record.name}"
    let candidate := matchingCandidates[0]!
    if matchedKeys.contains candidate.key then
      fail s!"multiple records matched declaration {record.name}"
    matchedKeys := matchedKeys.insert candidate.key
    let some command :=
        commandForKey? frontendResult.source frontendResult.commands candidate.key
      | fail s!"declaration syntax not found for {record.name}"
    let some (kind, range) := Corpus.SourceSyntax.proofRange? command
      | fail s!"proof syntax not found for {record.name}"
    edits := edits.push {
      declaration := record.name
      range
      replacement := replacementFor kind (commandIndent frontendResult.source command)
    }
  validateEdits frontendResult.source edits
  return edits

/-- Apply byte-range edits from the end of the file toward the beginning. -/
def applyEdits (source : String) (edits : Array Edit) : IO String := do
  validateEdits source edits
  let descending := edits.qsort fun a b => a.range.start.byteIdx > b.range.start.byteIdx
  let mut result := source
  for edit in descending do
    let before := String.Pos.Raw.extract result 0 edit.range.start
    let after := String.Pos.Raw.extract result edit.range.stop result.rawEndPos
    result := before ++ edit.replacement ++ after
  return result

/-- Reject edited text that produces an LSP error diagnostic. -/
def validateWithWorker (sourcePath : System.FilePath) (text : String)
    (timeoutMs : Nat := 60000) : IO Unit := do
  let absPath ← IO.FS.realPath sourcePath
  let uri := System.Uri.pathToUri absPath
  let pool ← Workers.WorkerPool.new (setsidWorkers := false)
  let worker ← Workers.Worker.spawn uri text pool.workerPath (setsid := false)
  try
    match (← worker.waitForDiagnostics timeoutMs) with
    | .timeout => fail s!"timed out validating {sourcePath}"
    | .workerExited => fail s!"Lean worker exited while validating {sourcePath}"
    | .done =>
        let some diagnostics ← worker.currentDiagnostics
          | fail s!"Lean worker returned no diagnostics for {sourcePath}"
        let errors := diagnostics.diagnostics.filter
          (·.severity? == some Lean.Lsp.DiagnosticSeverity.error)
        unless errors.isEmpty do
          let messages := "\n".intercalate (errors.toList.map (·.message))
          fail s!"Lean reported {errors.size} error(s) for {sourcePath}:\n{messages}"
  finally
    let _ ← worker.shutdown

/-- Rewrite one source file and validate the edited document before writing it. -/
unsafe def rewriteFile (config : RewriteConfig) : IO Unit := do
  let root ← IO.FS.realPath config.sourceRoot
  let relFile := normalizeRelativePath config.file
  let requestedPath : System.FilePath := relFile
  if requestedPath.isAbsolute then
    fail s!"--file must be project-relative: {config.file}"
  let sourcePath := root / relFile
  if !(← sourcePath.pathExists) then
    fail s!"source file does not exist: {sourcePath}"
  let cwd ← IO.currentDir
  let output :=
    if config.output.isAbsolute then config.output else cwd / config.output
  let outputAbs := output.normalize
  let sourceAbs ← IO.FS.realPath sourcePath
  unless isWithin root sourceAbs do
    fail s!"source file escapes --source-root: {config.file}"
  if outputAbs.toString == sourceAbs.toString then
    fail "output path must differ from the source file"
  if ← outputAbs.pathExists then
    let resolvedOutput ← IO.FS.realPath outputAbs
    if resolvedOutput.toString == sourceAbs.toString then
      fail "output path must not resolve to the source file"
  let some moduleName := Corpus.Discover.filePathToModule root sourceAbs
    | fail s!"cannot derive module name for {sourcePath}"
  let records ← selectTheorems (← readRecords config.records) relFile
  Corpus.Frontend.initFrontend
  let importLock : Corpus.Frontend.ImportLock ← Std.Mutex.new ()
  let frontendResult ← Corpus.Frontend.elaborateFile importLock {
    absPath := sourceAbs
    module := moduleName
    relPath := relFile
  }
  if frontendResult.hasErrors then
    fail s!"frontend elaboration failed for {sourcePath}"
  let edits ← planEdits frontendResult records
  let rewritten ← applyEdits frontendResult.source edits
  validateWithWorker sourceAbs rewritten
  if let some parent := outputAbs.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputAbs rewritten

end LeanReassemble
