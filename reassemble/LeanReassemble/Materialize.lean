import LeanReassemble.Rewrite
import LeanReassemble.Manifest
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
  producing the compilable reference state of the same records; `.delete` erases
  the declaration. See `ProofMode`. -/
  proofMode : ProofMode := .replace
  /-- Optional per-theorem action overrides; absent theorems use `proofMode`. -/
  manifestPath : Option System.FilePath := none
  /-- What to do when a theorem fails to reassemble. -/
  onFailure : FailurePolicy := .fail
  /-- Whether to KEEP evaluation commands (`#eval`, `#guard`, `#guard_msgs`, …) in
  the reassembled tree. They abort the build once a proof they transitively depend
  on is holed, so `materialize-repo` strips them by default whenever the run holes
  or deletes at least one proof. Set to skip that strip and preserve them verbatim
  (the historical behavior, and correct when nothing is holed). -/
  keepEval : Bool := false
  /-- Rewrite each source file in its own child process (the default). Each file's
  Lean environment then dies with its child, bounding peak memory to a single file
  rather than accumulating every module's imported environment in one long-lived
  process — which, on a large project like Cedar, otherwise climbs past 20 GiB and
  OOMs a swapless host. Set false (`--in-process`) to rewrite every file in this
  process instead: faster per file, but only safe for small projects.
  `materialize-units` is unaffected (it has its own per-target model). -/
  isolated : Bool := true

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

/-- Per-action tallies for a run. With a manifest, a single run can mix actions,
so the buckets are counted from each theorem's resolved mode rather than derived
from one global mode. `skipped`/`failed` come from the failure policy (Phase 3).
`auxiliary` counts theorem records that are not reassembly targets at all — `where`/
`let rec` helpers with no standalone declaration syntax (see `RecordPlan.auxiliary`;
`mutual` members are NOT auxiliary — they are holed in their own right); they are
excluded rather than holed, and this bucket keeps the accounting total whole. -/
structure RewriteCounts where
  replaced : Nat := 0
  preserved : Nat := 0
  deleted : Nat := 0
  skipped : Nat := 0
  failed : Nat := 0
  auxiliary : Nat := 0
  deriving ToJson, FromJson

/-- Add one resolved action to the tally. -/
def RewriteCounts.bump (counts : RewriteCounts) : ProofMode → RewriteCounts
  | .replace => { counts with replaced := counts.replaced + 1 }
  | .keep    => { counts with preserved := counts.preserved + 1 }
  | .delete  => { counts with deleted := counts.deleted + 1 }

/-- Sum two tallies field-wise — folds a per-file child's counts into the run total. -/
def RewriteCounts.add (a b : RewriteCounts) : RewriteCounts where
  replaced := a.replaced + b.replaced
  preserved := a.preserved + b.preserved
  deleted := a.deleted + b.deleted
  skipped := a.skipped + b.skipped
  failed := a.failed + b.failed
  auxiliary := a.auxiliary + b.auxiliary

/-- The rewrite summary. `proof_mode` reports the run default; the buckets report
the resolved action per theorem, so a manifest that mixes actions is reflected
faithfully. `failures` NAMES the theorems behind the `skipped`/`failed` counts (with
the reason each could not be reassembled), so a best-effort run is auditable rather
than only tallied; it is empty under `--on-failure fail`. -/
private def rewriteSummary (mode : ProofMode) (eligible : Nat)
    (counts : RewriteCounts) (failures : Array FailureReport := #[]) : Json :=
  Json.mkObj [
    ("proof_mode", toString mode),
    ("eligible", eligible),
    ("replaced", counts.replaced),
    ("preserved", counts.preserved),
    ("deleted", counts.deleted),
    ("skipped", counts.skipped),
    ("failed", counts.failed),
    ("auxiliary", counts.auxiliary),
    ("failures", failuresJson failures)
  ]

/-- Load the optional manifest and validate its keys against `eligible`. -/
private def loadManifest (path : Option System.FilePath)
    (eligible : Array Corpus.ConstRecord) : IO Manifest := do
  match path with
  | none => return Manifest.empty
  | some path =>
    let manifest ← Manifest.read path
    manifest.validateKeys (Std.HashSet.ofArray (eligible.map (·.name)))
    return manifest

/-- What rewriting ONE file into the artifact tree contributes to the run: the counts,
the named failures, and the per-file report entry. Serializable so an isolated child
can hand it back over stdout. -/
structure FileRewriteResult where
  relPath : String
  module : String
  edits : Nat
  evalStripped : Nat
  counts : RewriteCounts
  failures : Array FailureReport
  deriving ToJson, FromJson

/-- Rewrite ONE source file's proofs into `repoRoot / file`, applying the failure
policy and (when `stripEval`) erasing evaluation commands, and return the accumulation
the run folds in. Writes the rewritten file as a side effect. This is the unit of work
the isolated driver runs in a child process (see `rewriteOneFlag`); the in-process
driver calls it directly.

`prepareSourceFile` (frontend elaboration) sits OUTSIDE the failure policy: a module
that no longer elaborates is a file-level failure, not attributable to any one
theorem, so it aborts under every policy (as does the whole-tree build). skip/backoff
recover per-theorem PLANNING failures only — `skip` leaves a failed theorem's proof
untouched, `backoff` re-plans it as a delete. -/
unsafe def rewriteFileIntoRepo (sourceRoot : System.FilePath)
    (records : Array Corpus.ConstRecord) (file : String) (repoRoot : System.FilePath)
    (proofMode : ProofMode) (modeFor : String → ProofMode)
    (onFailure : FailurePolicy) (stripEval : Bool) : IO FileRewriteResult := do
  let prepared ← prepareSourceFile sourceRoot file
  let selected ← selectTheorems records prepared.relFile
  -- Plan resiliently in every policy: `planEditsCollecting` classifies each record as
  -- planned / auxiliary / failed. Auxiliaries (no standalone syntax) are counted and
  -- excluded under all policies; only `fail` re-throws on a genuine failure.
  let outcome ← planEditsCollecting prepared.frontendResult selected proofMode modeFor
  let mut counts : RewriteCounts := {}
  for edit in outcome.edits do
    counts := counts.bump (modeFor edit.declaration)
  counts := { counts with auxiliary := counts.auxiliary + outcome.auxiliaries.size }
  let mut edits : Array Edit := outcome.edits
  let mut failures : Array FailureReport := #[]
  if onFailure == .fail then
    if let some (_, reason) := outcome.failures[0]? then
      fail reason
  else if onFailure == .backoff then
    -- `backoff` retries the failed records as deletes; any that still cannot be planned
    -- fall through to a skip. `skip` records nothing further — the proof stays as-is.
    let failedNames := Std.HashSet.ofArray (outcome.failures.map (·.1))
    let failedRecords := selected.filter (failedNames.contains ·.name)
    let retry ← planEditsCollecting prepared.frontendResult failedRecords .delete
    edits := edits ++ retry.edits
    let retried := Std.HashSet.ofArray (retry.edits.map (·.declaration))
    counts := { counts with failed := counts.failed + retry.edits.size }
    counts := { counts with
      skipped := counts.skipped + (outcome.failures.size - retry.edits.size) }
    for (name, reason) in outcome.failures do
      let action := if retried.contains name then "failed" else "skipped"
      IO.eprintln s!"lean-reassemble: {action} {name}: {reason}"
      failures := failures.push { name, action, reason }
  else
    counts := { counts with skipped := counts.skipped + outcome.failures.size }
    for (name, reason) in outcome.failures do
      IO.eprintln s!"lean-reassemble: skipped {name}: {reason}"
      failures := failures.push { name, action := "skipped", reason }
  -- Merge eval-strip edits (if armed) into the proof edits: both come from the same
  -- `prepared.frontendResult`, so they share one coordinate space and one `applyEdits`
  -- pass (whose `validateEdits` still guards overlap).
  let stripped := if stripEval then evalStripEdits prepared.frontendResult else #[]
  let text ← applyEdits prepared.frontendResult.source (edits ++ stripped)
  let outputPath := repoRoot / file
  if let some parent := outputPath.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputPath text
  return { relPath := prepared.relFile, module := prepared.moduleName.toString,
           edits := edits.size, evalStripped := stripped.size, counts, failures }

/-- The complete request for one isolated file-rewrite child. Serialized as ONE JSON
argument so parent and child share a single encoding rather than a hand-written flag
pair (mirrors the extractor's `--internal-extract-one`). Nothing unserializable
crosses: the child re-derives `modeFor` from `records` + `manifestPath`. -/
structure RewriteOneRequest where
  sourceRoot : System.FilePath
  records : System.FilePath
  file : String
  repoRoot : System.FilePath
  proofMode : ProofMode
  manifestPath : Option System.FilePath
  onFailure : FailurePolicy
  stripEval : Bool
  deriving ToJson, FromJson

/-- The flag that carries a `RewriteOneRequest` to a child process. -/
def rewriteOneFlag : String := "--internal-rewrite-one"

/-- Child entry: rewrite one file per a `RewriteOneRequest` and print its
`FileRewriteResult` as compressed JSON on stdout. Runs in a fresh process so the
file's Lean environment is reclaimed on exit — the whole point of isolated mode. -/
unsafe def rewriteOneChild (request : RewriteOneRequest) : IO Unit := do
  let records ← readRecords request.records
  let theorems ← eligibleTheorems records
  let manifest ← loadManifest request.manifestPath theorems
  let modeFor := fun name => manifest.actionFor name request.proofMode
  let result ← rewriteFileIntoRepo request.sourceRoot records request.file
    request.repoRoot request.proofMode modeFor request.onFailure request.stripEval
  IO.println (toJson result).compress

/-- Run one file's rewrite in a child process and read back its `FileRewriteResult`.
The child inherits this (already `lake env`-re-exec'd) process's environment, so its
`prepareSourceFile` resolves imports from the same `LEAN_PATH`. A nonzero exit is a
hard failure — the module no longer elaborates, or `--on-failure fail` hit a genuine
per-theorem failure — and aborts the run, exactly as the in-process path would. -/
unsafe def rewriteFileViaChild (exe : System.FilePath) (request : RewriteOneRequest)
    : IO FileRewriteResult := do
  let child ← IO.Process.spawn {
    cmd := exe.toString
    args := #[rewriteOneFlag, (toJson request).compress]
    stdin := .null, stdout := .piped, stderr := .inherit
    -- `setsid` so a kill reaches any nested work, mirroring the extractor's children.
    setsid := true
  }
  -- Drain stdout on a task while waiting, so a child can never block on a full pipe.
  let stdoutTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let code ← child.wait
  let out ← IO.ofExcept (← IO.wait stdoutTask)
  if code != 0 then
    fail s!"rewriting {request.file} failed (child exited {code})"
  match Json.parse out >>= fromJson? (α := FileRewriteResult) with
  | .ok result => return result
  | .error e => fail s!"could not parse child result for {request.file}: {e}\n{out}"

unsafe def materializeRepo (config : MaterializeConfig) : IO Unit := do
  let (sourceRoot, artifact) ← prepareOutput config.sourceRoot config.output
  let records ← readRecords config.records
  let theorems ← eligibleTheorems records
  let manifest ← loadManifest config.manifestPath theorems
  let modeFor := fun name => manifest.actionFor name config.proofMode
  let name ← projectName sourceRoot
  let repoRel : System.FilePath := ("repos" : System.FilePath) / name
  let repoRoot := artifact / repoRel
  copyTree sourceRoot repoRoot
  removeIfExists (repoRoot / ".git")
  removeIfExists (repoRoot / ".lake")
  -- Evaluation commands (`#eval`, `#guard_msgs`, …) abort once a proof they reach
  -- through is holed, so we strip them WHEN the run actually holes or deletes a
  -- proof. `.keep` on its own holes nothing (the artifact is byte-faithful and would
  -- build untouched), so we only arm stripping when the resolved actions include a
  -- `.replace`/`.delete` — either from the default mode or a manifest override. The
  -- gate is run-level, not per-file: a `#eval` in a record-free module still breaks
  -- if it imports a holed proof, so those files must be stripped too. `--keep-eval`
  -- forces it off.
  let holingModes : Bool :=
    theorems.any fun t => modeFor t.name != ProofMode.keep
  let stripEval := !config.keepEval && holingModes
  let mut counts : RewriteCounts := {}
  let mut failures : Array FailureReport := #[]
  let mut rewrittenFiles : Array Json := #[]
  -- Files that carry theorem records are rewritten below; track them so the later
  -- eval-strip pass skips them (their eval edits are merged in here, in the SAME
  -- coordinate space as their proof edits) and only visits record-free modules.
  let mut rewrittenPaths : Std.HashSet String := {}
  -- Each file is rewritten by `rewriteFileIntoRepo`. In isolated mode (the default)
  -- that runs in a fresh child process per file, so the file's Lean environment dies
  -- with the child — bounding peak memory to one file rather than accumulating every
  -- module's imported environment in one long-lived process (which OOMs a large
  -- project like Cedar). `--in-process` runs them all here instead.
  let exe ← IO.appPath
  for file in theoremFiles theorems do
    let result ←
      if config.isolated then
        rewriteFileViaChild exe {
          sourceRoot, records := config.records, file, repoRoot,
          proofMode := config.proofMode, manifestPath := config.manifestPath,
          onFailure := config.onFailure, stripEval }
      else
        rewriteFileIntoRepo sourceRoot records file repoRoot
          config.proofMode modeFor config.onFailure stripEval
    counts := counts.add result.counts
    failures := failures ++ result.failures
    rewrittenPaths := rewrittenPaths.insert result.relPath
    rewrittenFiles := rewrittenFiles.push <| Json.mkObj [
      ("file", file),
      ("module", result.module),
      ("edits", result.edits),
      ("eval_stripped", result.evalStripped)
    ]
  -- Second pass: record-free modules the theorem loop never touched can still hold
  -- `#eval`s that reach a holed proof through imports (e.g. an `Examples.lean` with
  -- no theorems of its own). Strip those in place so the whole tree builds. A cheap
  -- textual prefilter (an eval command always writes one of these tokens) avoids
  -- elaborating the many files that carry none — in practice eval commands cluster
  -- in one or two modules per project.
  if stripEval then
    for df in ← Corpus.Discover.discoverFiles sourceRoot #[] do
      if rewrittenPaths.contains df.relPath then continue
      let raw ← IO.FS.readFile df.absPath
      let mentionsEval := ["#eval", "#reduce", "#guard"].any fun tok =>
        (raw.splitOn tok).length > 1
      unless mentionsEval do continue
      -- A record-free file that does not elaborate standalone (e.g. a `SymTest/`
      -- harness whose modules the default `lake build` target never builds, so its
      -- imports are not on `LEAN_PATH`) is not part of the build we verify below, so
      -- its `#eval`s cannot reach a holed proof through it. We cannot strip what we
      -- cannot elaborate, so skip it with a warning rather than aborting the whole
      -- run — unlike a theorem file, whose elaboration failure IS fatal above. If such
      -- a file really were in the build target, the final `lake build` would surface
      -- the break as an attributable error.
      let prepared ← try
          pure (some (← prepareSourceFile sourceRoot df.relPath))
        catch _ =>
          IO.eprintln s!"lean-reassemble: skipped eval-strip for {df.relPath} \
            (does not elaborate standalone; not in the build target)"
          pure none
      let some prepared := prepared | continue
      let stripped := evalStripEdits prepared.frontendResult
      if stripped.isEmpty then continue
      let text ← applyEdits prepared.frontendResult.source stripped
      IO.FS.writeFile (repoRoot / df.relPath) text
      rewrittenFiles := rewrittenFiles.push <| Json.mkObj [
        ("file", df.relPath),
        ("module", prepared.moduleName.toString),
        ("edits", 0),
        ("eval_stripped", stripped.size)
      ]
  -- Every eligible theorem is accounted for exactly once: as a resolved action
  -- (replaced/preserved/deleted), a backoff deletion (`failed`), a `skipped`, or an
  -- `auxiliary` (no standalone syntax, so excluded rather than holed).
  let accounted := counts.replaced + counts.preserved + counts.deleted
    + counts.skipped + counts.failed + counts.auxiliary
  if accounted != theorems.size then
    fail s!"theorem accounting mismatch: expected {theorems.size}, accounted {accounted} \
      (proof mode: {config.proofMode}, on-failure: {config.onFailure})"
  -- Best-effort build. A post-rewrite build break is usually at a DEPENDENT of a
  -- holed/deleted theorem, not at that theorem, so there is no safe theorem to
  -- auto-attribute it to — skip/backoff recover planning failures, not build
  -- breaks. We therefore let a build failure abort even under skip/backoff.
  let _ ← runChecked repoRoot "lake" (buildArgs config.buildTarget) cleanLakeEnv
  let report := Json.mkObj [
    ("format", "lean-corpus-rewrite-report.v1"),
    ("files", Json.arr rewrittenFiles),
    ("rewrite_summary", rewriteSummary config.proofMode theorems.size counts failures),
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
    ("rewrite_summary", rewriteSummary config.proofMode theorems.size counts failures),
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
  let manifest ← loadManifest config.manifestPath theorems
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
  let mut counts : RewriteCounts := {}
  let mut failures : Array FailureReport := #[]
  for index in [:theorems.size] do
    let record := theorems[index]!
    let targetMode := manifest.actionFor record.name config.proofMode
    -- A unit is the problem "reconstruct THIS theorem", so a `delete` target has no
    -- task to emit: deleting the very theorem a unit would ask a solver to prove is
    -- meaningless. Record it in the summary and move on. (`keep`/`sorry` neighbours
    -- are irrelevant here — a unit only ever touches its own target.)
    if targetMode == .delete then
      counts := counts.bump .delete
      continue
    -- A `where`/`let rec` helper or `mutual` member has no standalone declaration to
    -- reconstruct, so it is not a valid unit target ("prove this helper in isolation"
    -- is meaningless — it only exists inside its parent). Exclude it, like `delete`.
    let some prepared := preparedByFile[normalizeRelativePath record.file.get!]?
      | fail s!"prepared source missing for {record.name}"
    if (← planEditsCollecting prepared.frontendResult #[record] targetMode).auxiliaries.size == 1 then
      counts := { counts with auxiliary := counts.auxiliary + 1 }
      continue
    -- Build and verify the task, tolerating a per-task failure per `--on-failure`.
    -- The whole body is attributable to this one record, so `skip` (omit + record)
    -- and `backoff` (drop + record) are both clean here; only `fail` re-throws.
    let outcome : Except String Json ← try
      let file := normalizeRelativePath record.file.get!
      let some prepared := preparedByFile[file]?
        | fail s!"prepared source missing for {record.name}"
      -- A unit is a task for ONE theorem: hole out only this record's proof and
      -- leave every other declaration in the module intact. Rewriting the whole
      -- file's records here would sorry the target's neighbours too — including
      -- lemmas its own proof depends on — and would make every task from a given
      -- file byte-identical.
      let rewritten ← rewritePreparedFile prepared #[record] targetMode
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
        -- `.keep` adds nothing (delete emits no task, so it never reaches here). Only
        -- `.replace` introduces a fresh sorry.
        if targetMode == .keep then sourceSorryCount
        -- The target itself is holed out; if it was already incomplete it is counted
        -- in the baseline, so it must not be counted twice.
        else if record.axioms.contains "sorryAx" then sourceSorryCount
        else sourceSorryCount + 1
      if sorryWarnings.length > expectedSorries then
        fail s!"{record.name}: {sorryWarnings.length} `sorry` warning(s) but at most \
          {expectedSorries} expected for proof mode {targetMode} \
          ({sourceSorryCount} declaration(s) in this module are already incomplete \
          in the source): {"; ".intercalate sorryWarnings}"
      for line in diagnostics.splitOn "\n" do
        if line.contains "warning:" && !line.contains "declaration uses `sorry`" then
          fail s!"unexpected warning while verifying {record.name}: {line}"
      writeJson (artifact / taskRel / "task.json")
        (unitTaskJson id sourceRel toolchain (toString targetMode) record span
          leanRoots nativeRoots diagnostics)
      pure <| Except.ok <| Json.mkObj [
        ("id", id),
        ("target", record.name),
        ("task", artifactPath (taskRel / "task.json"))
      ]
    catch error =>
      if config.onFailure == .fail then throw error
      pure <| Except.error (error.toString.dropPrefix "lean-reassemble: ").copy
    match outcome with
    | .ok task =>
      counts := counts.bump targetMode
      tasks := tasks.push task
    | .error reason =>
      -- The task's src tree may have been partly written before the failure (the
      -- `id`/dir are a deterministic function of index+name, so recompute them here
      -- rather than threading them out of the try). Remove it so a skipped/backed-off
      -- theorem leaves no orphan directory in the artifact.
      removeIfExists (artifact / "units" / s!"{index}-{safeName record.name}")
      -- Under both surviving policies the theorem contributes no task; they differ
      -- only in which bucket records it. `backoff` deletes the offender, which in
      -- units mode is the same as skipping — there is no dependent to protect.
      let action := match config.onFailure with
        | FailurePolicy.skip => "skipped"
        | _                  => "failed"
      match config.onFailure with
      | FailurePolicy.skip => counts := { counts with skipped := counts.skipped + 1 }
      | _                  => counts := { counts with failed := counts.failed + 1 }
      IO.eprintln s!"lean-reassemble: {action} {record.name}: {reason}"
      failures := failures.push { name := record.name, action, reason }
  removeIfExists (artifact / ".work")
  let name ← projectName sourceRoot
  writeJson (artifact / "manifest.json") <| Json.mkObj [
    ("format", "lean-corpus-reassembly.v1"),
    ("mode", "units"),
    ("project", name),
    ("build_target", toJson config.buildTarget),
    ("environment", "cache/environment.json"),
    ("tasks", Json.arr tasks),
    ("rewrite_summary", rewriteSummary config.proofMode theorems.size counts failures),
    ("verification", Json.mkObj [("status", "passed")])
  ]

/-- Rewrite one source file and validate the edited document before writing it. -/
unsafe def rewriteFile (config : RewriteConfig) : IO Unit := do
  let cwd ← IO.currentDir
  let output :=
    if config.output.isAbsolute then config.output else cwd / config.output
  let outputAbs := output.normalize
  let records ← readRecords config.records
  -- Validate manifest keys against EVERY theorem in the records, not just this
  -- file's. A records file (and a manifest) commonly spans a whole project, and
  -- rewrite-file just happens to touch one file of it; a manifest key naming a real
  -- theorem in another file is not a typo. selectTheorems below still restricts the
  -- rewrite to this file's records.
  let manifest ← loadManifest config.manifestPath (← eligibleTheorems records)
  let modeFor := fun name => manifest.actionFor name config.proofMode
  let prepared ← prepareSourceFile config.sourceRoot config.file
  let selected ← selectTheorems records prepared.relFile
  -- Honor --on-failure: `fail` is the strict path; `skip`/`backoff` plan resiliently
  -- and act on each per-record failure. (rewrite-file does not build, so there is no
  -- whole-tree build surface here — only planning failures arise.)
  let edits ←
    if config.onFailure == .fail then
      planEdits prepared.frontendResult selected config.proofMode modeFor
    else do
      let outcome ← planEditsCollecting prepared.frontendResult selected
        config.proofMode modeFor
      for (name, reason) in outcome.failures do
        IO.eprintln s!"lean-reassemble: {config.onFailure} {name}: {reason}"
      if config.onFailure == .backoff then
        let failedNames := Std.HashSet.ofArray (outcome.failures.map (·.1))
        let failedRecords := selected.filter (failedNames.contains ·.name)
        let retry ← planEditsCollecting prepared.frontendResult failedRecords .delete
        pure (outcome.edits ++ retry.edits)
      else pure outcome.edits
  let text ← applyEdits prepared.frontendResult.source edits
  validateWithWorker prepared.sourceAbs text
  if outputAbs.toString == prepared.sourceAbs.toString then
    fail "output path must differ from the source file"
  if ← outputAbs.pathExists then
    let resolvedOutput ← IO.FS.realPath outputAbs
    if resolvedOutput.toString == prepared.sourceAbs.toString then
      fail "output path must not resolve to the source file"
  if let some parent := outputAbs.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile outputAbs text

end LeanReassemble
