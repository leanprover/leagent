import LeanReassemble.Rewrite
import Corpus.Artifact

namespace LeanReassemble

open Lean
-- One shared implementation with the extractor: `--decl` names its output
-- directory with the same function that names a unit task id here, so the two
-- artifacts correspond by construction rather than by convention.
open Corpus.Artifact (safeName)

structure MaterializeConfig where
  sourceRoot : System.FilePath
  records : System.FilePath
  output : System.FilePath
  buildTarget : Option String := none
  /-- `.replace` (default) holes out each selected proof; `.keep` preserves them,
  producing the compilable reference state of the same records. See `ProofMode`. -/
  proofMode : ProofMode := .replace

private def fail {α} (message : String) : IO α :=
  throw <| IO.userError s!"lean-reassemble: {message}"

private def normalizeRelativePath (path : String) : String :=
  ((path.dropPrefix "./").copy.dropPrefix ".\\").copy

private def isWithin (root path : System.FilePath) : Bool :=
  let root := root.normalize.toString
  let path := path.normalize.toString
  path == root || path.startsWith (root ++ "/") || path.startsWith (root ++ "\\")

private def artifactPath (path : System.FilePath) : String :=
  path.toString.replace "\\" "/"

private def writeJson (path : System.FilePath) (json : Json) : IO Unit :=
  IO.FS.writeFile path (json.pretty ++ "\n")

private def runOutput (cwd : System.FilePath) (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output :=
  IO.Process.output { cmd, args, cwd := some cwd, env }

private def runChecked (cwd : System.FilePath) (cmd : String) (args : Array String)
    (env : Array (String × Option String) := #[]) : IO IO.Process.Output := do
  let output ← runOutput cwd cmd args env
  if output.exitCode != 0 then
    fail s!"command failed ({output.exitCode}): {cmd} {String.intercalate " " args.toList}\n\
      {output.stdout}{output.stderr}"
  return output

private def cleanLakeEnv : Array (String × Option String) :=
  #[("LEAN_PATH", none), ("LD_LIBRARY_PATH", none)]

private def copyTree (source destination : System.FilePath) : IO Unit := do
  IO.FS.createDirAll destination
  let sourceContents := source.toString ++ System.FilePath.pathSeparator.toString ++ "."
  let _ ← runChecked destination "cp" #["-a", sourceContents, destination.toString]

private def copyCacheTree (source destination : System.FilePath) : IO Unit := do
  IO.FS.createDirAll destination
  let sourceContents := source.toString ++ System.FilePath.pathSeparator.toString ++ "."
  let _ ← runChecked destination "cp" #["-aL", sourceContents, destination.toString]

private def removeIfExists (path : System.FilePath) : IO Unit := do
  try
    if (← path.symlinkMetadata).type == .dir then
      IO.FS.removeDirAll path
    else
      IO.FS.removeFile path
  catch error =>
    if ← path.pathExists then throw error

private def pathEntryExists (path : System.FilePath) : IO Bool := do
  try
    let _ ← path.symlinkMetadata
    return true
  catch _ =>
    return false

private partial def resolveForCreation (path : System.FilePath) : IO System.FilePath := do
  if ← pathEntryExists path then
    return ← IO.FS.realPath path
  let some parent := path.parent
    | fail s!"cannot resolve output path: {path}"
  let some name := path.fileName
    | fail s!"cannot resolve output path: {path}"
  return (← resolveForCreation parent) / name

private def prepareOutput (sourceRoot output : System.FilePath) :
    IO (System.FilePath × System.FilePath) := do
  let source ← IO.FS.realPath sourceRoot
  if !(← (source / "lake-manifest.json").pathExists) then
    fail s!"lake-manifest.json does not exist in {source}"
  let cwd ← IO.currentDir
  let requested := (if output.isAbsolute then output else cwd / output).normalize
  if ← pathEntryExists requested then
    fail s!"output already exists: {requested}"
  let artifact ← resolveForCreation requested
  if isWithin source artifact then
    fail "output must be outside --source-root"
  IO.FS.createDirAll artifact
  return (source, artifact)

private def eligibleTheorems (records : Array Corpus.ConstRecord) :
    IO (Array Corpus.ConstRecord) := do
  let mut result := #[]
  for record in records do
    if Corpus.Artifact.isTheoremRecord record then
      if record.file.isNone then
        fail s!"theorem record {record.name} has no file"
      result := result.push record
  if result.isEmpty then
    fail "no theorem records found"
  return result

private def theoremFiles (records : Array Corpus.ConstRecord) : Array String := Id.run do
  let mut result := #[]
  let mut seen : Std.HashSet String := {}
  for record in records do
    if let some file := record.file then
      let file := normalizeRelativePath file
      if !seen.contains file then
        seen := seen.insert file
        result := result.push file
  return result.qsort (· < ·)

/-- How many of `records` belonging to `file` were ALREADY incomplete in the source
(their transitive axioms include `sorryAx`). Those declarations warn when the module
is compiled no matter what we rewrite, so they set the baseline a unit's `sorry`
warnings are measured against.

Only theorem records carry `axioms`, and only records for this file matter, since a
unit compiles exactly one module. -/
private def sourceSorryCountFor (records : Array Corpus.ConstRecord) (file : String)
    : Nat :=
  records.foldl (init := 0) fun acc record =>
    match record.file with
    | some recordFile =>
        if normalizeRelativePath recordFile == file && record.axioms.contains "sorryAx"
        then acc + 1 else acc
    | none => acc

private def buildArgs (target : Option String) : Array String :=
  #["build"] ++ target.toArray

private def projectName (root : System.FilePath) : IO String :=
  match root.fileName with
  | some name => pure name
  | none => fail s!"cannot derive project name from {root}"

/-- The rewrite summary. `replaced` counts proofs turned into `sorry`; under
`.keep` nothing is replaced, and `preserved` reports the same edits instead — the
proofs were located and validated, just written back unchanged. -/
private def rewriteSummary (mode : ProofMode) (eligible edits : Nat) : Json :=
  Json.mkObj [
    ("proof_mode", toString mode),
    ("eligible", eligible),
    ("replaced", if mode == .keep then 0 else edits),
    ("preserved", if mode == .keep then edits else 0),
    ("skipped", 0),
    ("failed", 0)
  ]

unsafe def materializeRepo (config : MaterializeConfig) : IO Unit := do
  let (sourceRoot, artifact) ← prepareOutput config.sourceRoot config.output
  let records ← readRecords config.records
  let theorems ← eligibleTheorems records
  let name ← projectName sourceRoot
  let repoRel : System.FilePath := ("repos" : System.FilePath) / name
  let repoRoot := artifact / repoRel
  copyTree sourceRoot repoRoot
  removeIfExists (repoRoot / ".git")
  removeIfExists (repoRoot / ".lake")
  let mut replaced := 0
  let mut rewrittenFiles : Array Json := #[]
  for file in theoremFiles theorems do
    let result ← rewriteSourceFile sourceRoot records file config.proofMode
    let outputPath := repoRoot / file
    if let some parent := outputPath.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile outputPath result.text
    replaced := replaced + result.edits.size
    rewrittenFiles := rewrittenFiles.push <| Json.mkObj [
      ("file", file),
      ("module", result.moduleName.toString),
      ("edits", result.edits.size)
    ]
  if replaced != theorems.size then
    fail s!"edit count mismatch: expected {theorems.size} theorem(s), \
      edited {replaced} (proof mode: {config.proofMode})"
  let _ ← runChecked repoRoot "lake" (buildArgs config.buildTarget) cleanLakeEnv
  let report := Json.mkObj [
    ("format", "lean-corpus-rewrite-report.v1"),
    ("files", Json.arr rewrittenFiles),
    ("rewrite_summary", rewriteSummary config.proofMode theorems.size replaced),
    ("verification", Json.mkObj [("status", "passed"), ("command",
      String.intercalate " " (["lake", "build"] ++ config.buildTarget.toList))])
  ]
  writeJson (repoRoot / "rewrite-report.json") report
  writeJson (artifact / "manifest.json") <| Json.mkObj [
    ("format", "lean-corpus-reassembly.v1"),
    ("mode", "repos"),
    ("project", name),
    ("repository", artifactPath repoRel),
    ("build_target", toJson config.buildTarget),
    ("rewrite_summary", rewriteSummary config.proofMode theorems.size replaced),
    ("verification", Json.mkObj [("status", "passed")])
  ]

private def splitSearchPath (value : String) : Array System.FilePath :=
  (System.SearchPath.parse value.trimAscii.copy).toArray.filter
    (fun path => !path.toString.isEmpty)

private def captureEnv (root : System.FilePath) (name : String) :
    IO (Array System.FilePath) := do
  let output ← runOutput root "lake" #["env", "printenv", name] cleanLakeEnv
  if output.exitCode == 0 then
    return splitSearchPath output.stdout
  if output.exitCode == 1 && output.stdout.isEmpty then
    return #[]
  fail s!"failed to capture {name}: {output.stdout}{output.stderr}"

private def copySearchRoots (artifact sysroot : System.FilePath)
    (roots : Array System.FilePath) : IO (Array String) := do
  let mut copied := #[]
  for root in roots do
    if ← root.pathExists then
      let absolute ← IO.FS.realPath root
      if !isWithin sysroot absolute then
        let relative : System.FilePath :=
          ("cache" : System.FilePath) / "roots" / toString copied.size
        copyCacheTree absolute (artifact / relative)
        copied := copied.push (artifactPath relative)
  return copied

private def copyNativeRoots (artifact sysroot : System.FilePath)
    (roots : Array System.FilePath) : IO (Array String) := do
  let mut copied := #[]
  for root in roots do
    if ← root.pathExists then
      let absolute ← IO.FS.realPath root
      if !isWithin sysroot absolute then
        let relative : System.FilePath :=
          ("cache" : System.FilePath) / "native" / toString copied.size
        let destination := artifact / relative
        IO.FS.createDirAll destination
        for entry in (← absolute.readDir) do
          unless ← entry.path.isDir do
            let _ ← runChecked destination "cp" #["-aL", entry.path.toString,
              destination.toString]
        copied := copied.push (artifactPath relative)
  return copied

private def absoluteArtifactPaths (artifact : System.FilePath)
    (paths : Array String) : Array String :=
  paths.map fun (path : String) => (artifact / (path : System.FilePath)).toString

private def envValue (paths : Array String) : String :=
  System.SearchPath.toString (paths.toList.map System.FilePath.mk)

private def replacementSpan? (edits : Array Edit) (declaration : String) :
    Option (Nat × Nat) := Id.run do
  let ascending := edits.qsort fun a b => a.range.start.byteIdx < b.range.start.byteIdx
  let mut sourceCursor := 0
  let mut outputCursor := 0
  for edit in ascending do
    let start := outputCursor + edit.range.start.byteIdx - sourceCursor
    let stop := start + edit.replacement.utf8ByteSize
    if edit.declaration == declaration then
      return some (start, stop)
    sourceCursor := edit.range.stop.byteIdx
    outputCursor := stop
  return none

private def unitTaskJson (id sourceRel toolchain proofMode : String)
    (record : Corpus.ConstRecord)
    (span : Nat × Nat) (leanRoots nativeRoots : Array String)
    (diagnostics : String) : Json :=
  let srcRoot := s!"units/{id}/src"
  Json.mkObj [
    ("format", "lean-corpus-task.v1"),
    ("id", id),
    ("target", record.name),
    ("module", record.module),
    ("source", sourceRel),
    ("toolchain", toolchain),
    ("command", Json.arr #[
      "elan", "run", toolchain, "lean", "-R", srcRoot, sourceRel
    ]),
    ("replacement", Json.mkObj [("start_byte", span.1), ("end_byte", span.2)]),
    ("lean_path", Json.arr (leanRoots.map Json.str)),
    ("ld_library_path", Json.arr (nativeRoots.map Json.str)),
    ("proof_mode", proofMode),
    ("verification", Json.mkObj [
      ("status", "passed"),
      ("exit_code", 0),
      ("diagnostics", diagnostics)
    ])
  ]

unsafe def materializeUnits (config : MaterializeConfig) : IO Unit := do
  let (sourceRoot, artifact) ← prepareOutput config.sourceRoot config.output
  let records ← readRecords config.records
  let theorems ← eligibleTheorems records
  let workRoot := artifact / ".work" / "pristine"
  copyTree sourceRoot workRoot
  removeIfExists (workRoot / ".git")
  removeIfExists (workRoot / ".lake")
  let _ ← runChecked workRoot "lake" (buildArgs config.buildTarget) cleanLakeEnv
  let leanPath ← captureEnv workRoot "LEAN_PATH"
  let nativePath ← captureEnv workRoot "LD_LIBRARY_PATH"
  let prefixOutput ← runChecked workRoot "lake" #["env", "lean", "--print-prefix"] cleanLakeEnv
  let sysroot ← IO.FS.realPath prefixOutput.stdout.trimAscii.copy
  let githashOutput ← runChecked workRoot "lake" #["env", "lean", "--githash"] cleanLakeEnv
  let toolchain ← if ← (workRoot / "lean-toolchain").pathExists then do
    let contents ← IO.FS.readFile (workRoot / "lean-toolchain")
    pure contents.trimAscii.copy
  else
    pure ""
  if toolchain.isEmpty then
    fail "lean-toolchain is missing or empty"
  let leanRoots ← copySearchRoots artifact sysroot leanPath
  let nativeRoots ← copyNativeRoots artifact sysroot nativePath
  let environment := Json.mkObj [
    ("toolchain", toolchain),
    ("lean_githash", githashOutput.stdout.trimAscii.copy),
    ("lean_path", Json.arr (leanRoots.map Json.str)),
    ("ld_library_path", Json.arr (nativeRoots.map Json.str))
  ]
  IO.FS.createDirAll (artifact / "cache")
  writeJson (artifact / "cache" / "environment.json") environment
  let leanExe := sysroot / "bin" / "lean"
  let leanEnv := #[
    ("LEAN_PATH", some (envValue (absoluteArtifactPaths artifact leanRoots))),
    ("LD_LIBRARY_PATH", some (envValue (absoluteArtifactPaths artifact nativeRoots)))
  ]
  -- Elaborate each source file ONCE, then derive a per-target rewrite from it.
  -- Elaboration is the expensive step, so it is shared; the cheap byte-splice is
  -- what varies per task.
  let mut preparedByFile : Std.HashMap String PreparedFile := {}
  for file in theoremFiles theorems do
    preparedByFile := preparedByFile.insert file (← prepareSourceFile sourceRoot file)
  let mut tasks : Array Json := #[]
  for index in [:theorems.size] do
    let record := theorems[index]!
    let file := normalizeRelativePath record.file.get!
    let some prepared := preparedByFile[file]?
      | fail s!"prepared source missing for {record.name}"
    -- A unit is a task for ONE theorem: hole out only this record's proof and
    -- leave every other declaration in the module intact. Rewriting the whole
    -- file's records here would sorry the target's neighbours too — including
    -- lemmas its own proof depends on — and would make every task from a given
    -- file byte-identical.
    let rewritten ← rewritePreparedFile prepared #[record] config.proofMode
    if rewritten.moduleName.toString != record.module then
      fail s!"module mismatch for {record.name}"
    let some span := replacementSpan? rewritten.edits record.name
      | fail s!"replacement span missing for {record.name}"
    let id := s!"{index}-{safeName record.name}"
    let taskRel : System.FilePath := ("units" : System.FilePath) / id
    let srcRoot := artifact / taskRel / "src"
    let sourcePath := srcRoot / file
    if let some parent := sourcePath.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile sourcePath rewritten.text
    let verification ← runOutput artifact leanExe.toString
      #["-R", srcRoot.toString, sourcePath.toString] leanEnv
    if verification.exitCode != 0 then
      fail s!"unit verification failed for {record.name}:\n\
        {verification.stdout}{verification.stderr}"
    let sourceRel := artifactPath (taskRel / "src" / file)
    let diagnostics := (verification.stdout ++ verification.stderr).replace
      artifact.toString "."
    -- `sorry` warnings are expected under `.replace` (we just created one) and,
    -- under EITHER mode, for declarations whose proof was already incomplete in the
    -- source. Real projects carry work-in-progress `sorry`s, and the module retains
    -- every declaration, so those warnings are not ours to reject: the extractor
    -- records them as `sorryAx` in the record's `axioms`, and rejecting them would
    -- make `--proofs keep` unusable on any project with an open goal.
    --
    -- What we DO reject under `.keep` is a `sorry` count higher than the source
    -- explains — that would mean we holed out a proof we were told to preserve.
    let sorryWarnings := (diagnostics.splitOn "\n").filter
      (fun line => line.contains "warning:" && line.contains "declaration uses `sorry`")
    let sourceSorryCount := sourceSorryCountFor records file
    let expectedSorries :=
      if config.proofMode == .keep then sourceSorryCount
      -- The target itself is holed out; if it was already incomplete it is counted
      -- in the baseline, so it must not be counted twice.
      else if record.axioms.contains "sorryAx" then sourceSorryCount
      else sourceSorryCount + 1
    if sorryWarnings.length > expectedSorries then
      fail s!"{record.name}: {sorryWarnings.length} `sorry` warning(s) but at most \
        {expectedSorries} expected for proof mode {config.proofMode} \
        ({sourceSorryCount} declaration(s) in this module are already incomplete \
        in the source): {"; ".intercalate sorryWarnings}"
    for line in diagnostics.splitOn "\n" do
      if line.contains "warning:" && !line.contains "declaration uses `sorry`" then
        fail s!"unexpected warning while verifying {record.name}: {line}"
    writeJson (artifact / taskRel / "task.json")
      (unitTaskJson id sourceRel toolchain (toString config.proofMode) record span
        leanRoots nativeRoots diagnostics)
    tasks := tasks.push <| Json.mkObj [
      ("id", id),
      ("target", record.name),
      ("task", artifactPath (taskRel / "task.json"))
    ]
  removeIfExists (artifact / ".work")
  let name ← projectName sourceRoot
  writeJson (artifact / "manifest.json") <| Json.mkObj [
    ("format", "lean-corpus-reassembly.v1"),
    ("mode", "units"),
    ("project", name),
    ("build_target", toJson config.buildTarget),
    ("environment", "cache/environment.json"),
    ("tasks", Json.arr tasks),
    ("rewrite_summary", rewriteSummary config.proofMode theorems.size theorems.size),
    ("verification", Json.mkObj [("status", "passed")])
  ]

end LeanReassemble
