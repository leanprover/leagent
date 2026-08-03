import Corpus.Artifact
import Corpus.CollectCommon
import Corpus.Frontend
import Corpus.Records
import Corpus.SourceSyntax
import Corpus.Verify
import Workers

namespace LeanReassemble

open Lean

/-- What to do with each selected theorem's proof.

`keep` is not a way of skipping the rewriter — it runs the SAME pipeline
(match records to declarations, agree on the proof range, check the recorded
`body` against the source) and only substitutes the original text for the
`sorry`. So a `keep` artifact is a *verified reference state*: proof of the
correspondence between records and source, in compilable form. -/
inductive ProofMode where
  /-- Replace each selected proof with `by sorry` (the default). -/
  | replace
  /-- Preserve each selected proof verbatim; output is byte-identical to source. -/
  | keep
  deriving Inhabited, BEq

def ProofMode.toString : ProofMode → String
  | .replace => "sorry"
  | .keep    => "keep"

instance : ToString ProofMode := ⟨ProofMode.toString⟩

structure RewriteConfig where
  sourceRoot : System.FilePath
  records : System.FilePath
  file : String
  output : System.FilePath
  proofMode : ProofMode := .replace

structure Edit where
  declaration : String
  range : Lean.Syntax.Range
  expected : String
  replacement : String
  deriving Inhabited, Repr

structure RewriteResult where
  sourcePath : System.FilePath
  moduleName : Name
  text : String
  edits : Array Edit

private structure Candidate where
  name : String
  key : Nat × Nat
  start : Nat × Nat
  deriving Inhabited

/-- Fail with the tool's diagnostic prefix. Shared across the reassembler. -/
def fail {α} (message : String) : IO α :=
  throw <| IO.userError s!"lean-reassemble: {message}"

/-- Strip a leading `./` or `.\` so record paths and CLI `--file` compare equal. -/
def normalizeRelativePath (path : String) : String :=
  ((path.dropPrefix "./").copy.dropPrefix ".\\").copy

/-- True iff `path` is `root` or lives beneath it. Both sides are normalized, so
callers need not pre-`realPath`. -/
def isWithin (root path : System.FilePath) : Bool :=
  let root := root.normalize.toString
  let path := path.normalize.toString
  path == root || path.startsWith (root ++ "/") || path.startsWith (root ++ "\\")

/-- Read and decode one JSON object per nonempty input line. Shares the extractor's
JSONL conventions via `Corpus.Artifact`, so writer and reader cannot drift. -/
def readRecords (path : System.FilePath) : IO (Array Corpus.ConstRecord) := do
  match Corpus.Artifact.parseJsonl (α := Corpus.ConstRecord) (← IO.FS.readFile path) with
  | .ok records => return records
  | .error error => fail s!"{path}: {error}"

/-- Select theorem records for one source file and reject ambiguous input. -/
def selectTheorems (records : Array Corpus.ConstRecord) (file : String) :
    IO (Array Corpus.ConstRecord) := do
  let requested := normalizeRelativePath file
  let mut selected := #[]
  let mut names : Std.HashSet String := {}
  for record in records do
    if Corpus.Artifact.isTheoremRecord record then
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
    Corpus.SourceSyntax.declarationKeys fileMap command |>.contains key

private def commandIndent (source : String) (command : Syntax) : String := Id.run do
  let some range := Corpus.SourceSyntax.commandRange? command | return ""
  let fileMap := source.toFileMap
  let position := fileMap.toPosition range.start
  let lineStart := fileMap.lineStart position.line
  let whitespace := String.Pos.Raw.extract source lineStart range.start
  if whitespace.all fun char => char == ' ' || char == '\t' then whitespace else ""

/-- The text that replaces one proof's source range.

Under `.keep` the replacement IS the original slice, so applying the edits is the
identity on the file. We deliberately keep it flowing through the edit machinery
rather than short-circuiting: the range still has to be found and validated, which
is what makes a kept artifact evidence that the records match the source. -/
private def replacementFor (mode : ProofMode)
    (kind : Corpus.SourceSyntax.DeclValueKind) (indent original : String) : String :=
  match mode with
  | .keep => original
  | .replace =>
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
    let actual := String.Pos.Raw.extract source edit.range.start edit.range.stop
    if actual != edit.expected then
      fail s!"source changed at proof range for {edit.declaration}"
  let ascending := edits.qsort fun a b => a.range.start.byteIdx < b.range.start.byteIdx
  for index in [1:ascending.size] do
    let previous := ascending[index - 1]!
    let current := ascending[index]!
    if current.range.start.byteIdx < previous.range.stop.byteIdx then
      fail s!"overlapping proof ranges for {previous.declaration} and {current.declaration}"

/-- Match records to declarations and compute non-overlapping source edits. -/
def planEdits (frontendResult : Corpus.Frontend.ElabResult)
    (records : Array Corpus.ConstRecord) (mode : ProofMode := .replace)
    : IO (Array Edit) := do
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
    let expected := String.Pos.Raw.extract frontendResult.source range.start range.stop
    if let some body := record.body then
      if expected.trimAsciiEnd.toString != body then
        fail s!"record body does not match source proof for {record.name}"
    edits := edits.push {
      declaration := record.name
      range
      expected
      replacement := replacementFor mode kind
        (commandIndent frontendResult.source command) expected
    }
  validateEdits frontendResult.source edits
  return edits

/-- Apply validated byte-range edits in one left-to-right pass. -/
def applyEdits (source : String) (edits : Array Edit) : IO String := do
  validateEdits source edits
  let ascending := edits.qsort fun a b => a.range.start.byteIdx < b.range.start.byteIdx
  let mut result := ""
  let mut cursor : String.Pos.Raw := 0
  for edit in ascending do
    result := result ++ String.Pos.Raw.extract source cursor edit.range.start
    result := result ++ edit.replacement
    cursor := edit.range.stop
  result := result ++ String.Pos.Raw.extract source cursor source.rawEndPos
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

/-- One source file, elaborated once, ready to be rewritten any number of ways.

Separated from `rewriteSourceFile` because `materialize-units` needs MANY rewrites
of the same file — one per target theorem — and elaboration is the expensive part.
Reusing this across targets keeps the cost one elaboration per file rather than one
per task. -/
structure PreparedFile where
  sourceAbs      : System.FilePath
  relFile        : String
  moduleName     : Name
  frontendResult : Corpus.Frontend.ElabResult

/-- Locate, validate, and elaborate one project-relative source file. -/
unsafe def prepareSourceFile (sourceRoot : System.FilePath) (file : String)
    : IO PreparedFile := do
  let root ← IO.FS.realPath sourceRoot
  let relFile := normalizeRelativePath file
  let requestedPath : System.FilePath := relFile
  if requestedPath.isAbsolute then
    fail s!"--file must be project-relative: {file}"
  let sourcePath := root / relFile
  if !(← sourcePath.pathExists) then
    fail s!"source file does not exist: {sourcePath}"
  let sourceAbs ← IO.FS.realPath sourcePath
  unless isWithin root sourceAbs do
    fail s!"source file escapes --source-root: {file}"
  let some moduleName := Corpus.Discover.filePathToModule root sourceAbs
    | fail s!"cannot derive module name for {sourcePath}"
  Corpus.Frontend.initFrontend
  let importLock : Corpus.Frontend.ImportLock ← Std.Mutex.new ()
  let frontendResult ← Corpus.Frontend.elaborateFile importLock {
    absPath := sourceAbs
    module := moduleName
    relPath := relFile
  }
  if frontendResult.hasErrors then
    fail s!"frontend elaboration failed for {sourcePath}"
  return { sourceAbs, relFile, moduleName, frontendResult }

/-- Rewrite an already-prepared file for a given set of records. -/
def rewritePreparedFile (prepared : PreparedFile)
    (selected : Array Corpus.ConstRecord) (mode : ProofMode := .replace)
    (validate : Bool := true) : IO RewriteResult := do
  let edits ← planEdits prepared.frontendResult selected mode
  let rewritten ← applyEdits prepared.frontendResult.source edits
  if validate then
    validateWithWorker prepared.sourceAbs rewritten
  return { sourcePath := prepared.sourceAbs, moduleName := prepared.moduleName,
           text := rewritten, edits }

/-- Rewrite one source file for every record that belongs to it. -/
unsafe def rewriteSourceFile (sourceRoot : System.FilePath)
    (records : Array Corpus.ConstRecord) (file : String)
    (mode : ProofMode := .replace) : IO RewriteResult := do
  let prepared ← prepareSourceFile sourceRoot file
  rewritePreparedFile prepared (← selectTheorems records prepared.relFile) mode

/-- Rewrite one source file and validate the edited document before writing it. -/
unsafe def rewriteFile (config : RewriteConfig) : IO Unit := do
  let cwd ← IO.currentDir
  let output :=
    if config.output.isAbsolute then config.output else cwd / config.output
  let outputAbs := output.normalize
  let result ← rewriteSourceFile config.sourceRoot (← readRecords config.records)
    config.file config.proofMode
  if outputAbs.toString == result.sourcePath.toString then
    fail "output path must differ from the source file"
  if ← outputAbs.pathExists then
    let resolvedOutput ← IO.FS.realPath outputAbs
    if resolvedOutput.toString == result.sourcePath.toString then
      fail "output path must not resolve to the source file"
  if let some parent := outputAbs.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputAbs result.text

end LeanReassemble
