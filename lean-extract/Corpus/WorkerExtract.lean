import Lean
import Corpus.Records
import Corpus.Tags
import Corpus.Discover
import Corpus.Frontend
import Corpus.CorpusManifest
import Corpus.Artifact
import Corpus.FileDriver
import Corpus.ChildProcess
import Lake.Build.Trace

/-!
Frontend-driven corpus extraction. Drives Lean's frontend via `Corpus.Frontend`:
isolated mode runs one frontend process per file, the optional shared-process mode
uses `elaborateFiles`.

Each `CorpusManifestEntry` is mapped to the `ConstRecord` JSONL schema. The client
supplies the `file` path (from discovery) and `tags` (from the local `TagConfig`)
and performs the kind-string mapping; the collector computes everything that needs
an `Environment`.
-/

namespace Corpus

open Lean

/-- Map the collector's kind label to the corpus schema's kind, applying the
`structure`/`inductive` distinction and the `private` prefix. Mirrors
`Extract.kindOf` + the private-prefix rule in `Extract.buildRecord`. -/
def mapKind (pluginKind : String) (isPrivate isStructure : Bool) : String :=
  let base := match pluginKind with
    | "definition"  => "def"
    | "theorem"     => "theorem"
    | "axiom"       => "axiom"
    | "opaque"      => "opaque"
    | "quotient"    => "quot"
    | "constructor" => "ctor"
    | "recursor"    => "rec"
    | "inductive"   => if isStructure then "structure" else "inductive"
    | other         => other
  if isPrivate && base == "theorem" then "private theorem"
  else if isPrivate && base == "def" then "private def"
  else base

/-- Map one `CorpusManifestEntry` to a `ConstRecord`. `relFile` is the
project-relative source path from discovery; `tagConfig` supplies `tags`. -/
def entryToRecord (e : CorpusManifestEntry) (relFile : String) (tagConfig : TagConfig)
    : ConstRecord :=
  { name        := e.name
    kind        := mapKind e.kind e.isPrivate e.isStructure
    module      := e.module
    file        := some relFile
    startLine   := e.startLine
    startCol    := e.startCol
    endLine     := e.endLine
    endCol      := e.endCol
    signature   := e.signature
    body        := e.body
    declSource  := e.declSource
    declNamespace := e.declNamespace
    scopePrelude  := e.scopePrelude.toList
    fileImports   := e.fileImports.toList
    type        := e.type
    value       := e.value?
    proofScript := e.proofScript
    proofMethod := e.proofMethod
    doc         := e.doc?
    deps        := e.deps.toList
    premises    := e.premises.toList
    axioms      := e.axioms.toList
    isProtected := e.isProtected
    isPrivate   := e.isPrivate
    tags        := tagConfig.matchTags e.module
    -- Proof-complexity metrics. When `e.metrics` is `none` (flag off) every
    -- tactic-family field keeps its record default; a term proof yields a metrics
    -- record with `isTermProof := true` and null tactic fields by construction.
    isTermProof       := (e.metrics.map (·.isTermProof)).getD false
    tacticMetricsSource := e.metricsSource
    tacticStepCount   := e.metrics.bind (·.tacticStepCount)
    tacticTotalCount  := e.metrics.bind (·.tacticTotalCount)
    maxTacticDepth    := e.metrics.bind (·.maxTacticDepth)
    tacticKinds       := (e.metrics.map (·.tacticKinds.toList)).getD []
    tacticHistogram   := (e.metrics.map (·.tacticHistogram.toList)).getD []
    caseSplitCount    := e.metrics.bind (·.caseSplitCount)
    rewriteCount      := e.metrics.bind (·.rewriteCount)
    haveCount         := e.metrics.bind (·.haveCount)
    calcSteps         := e.metrics.bind (·.calcSteps)
    automationTactics := (e.metrics.map (·.automationTactics.toList)).getD []
    proofTermSize     := e.proofTermSize
    proofTermDepth    := e.proofTermDepth
    attributes        := (e.metrics.map (·.attributes.toList)).getD [] }

/-- Extract the corpus entries for ONE already-elaborated file.

Reverse-elaboration is bounded COOPERATIVELY (there is no subprocess to kill in
the single-process model): the `reverseNodeCeiling` size pre-filter skips
pathological proof terms before any work, the per-theorem heartbeat budgets bound
the in-range ones, and the per-file wall-clock deadline (`reverseDeadlineMs`) sheds
the expensive tail between theorems. When `reverseElab` is requested we still make
TWO collector passes over the same (already-elaborated) environment:

  1. BASELINE — `reverseElab := false`: fast, captures every theorem/definition
     record (with `proofScript := none`).
  2. ENRICH — `reverseElab := true` under `manifestTimeoutMs`: the same records
     WITH proof scripts.

If the enrich pass throws (a pathological proof exhausting a bound), we already
hold the baseline, so we keep it and lose only this file's proof SCRIPTS, never its
records. Elaboration happens once; both passes fold the same environment, so the
baseline is cheap. -/
def extractFileEntries (r : Frontend.ElabResult) (opts : CollectOptions)
    (manifestTimeoutMs : Nat := 60000)
    : IO (Array CorpusManifestEntry) := do
  -- Baseline pass (no reverse-elab): the guaranteed record set.
  let baseline ← corpusManifestCore r
    { opts with reverseElab := false, reverseClosers := false }
  if !opts.reverseElab then
    return baseline
  -- Enrich pass (reverse-elab, optionally with closers) under the fold's internal
  -- wall-clock budget (80% of the per-file timeout, headroom for the rest). On any
  -- failure we fall back to the baseline so records survive.
  try
    corpusManifestCore r opts (FileDriver.deadlineFor manifestTimeoutMs)
  catch e =>
    IO.eprintln s!"corpus-extract: reverse-elab failed for {r.file.relPath} \
      ({e.toString}); kept {baseline.size} records without proof scripts"
    return baseline

/-- Summary of a corpus extraction run, for `metadata.json` / stderr reporting.
Corpus entries carry no per-entry `outcome`, so only the file counters of the shared
`FileDriver.FileStats` are populated. -/
abbrev WorkerRunStats := FileDriver.FileStats


/-- Extract one discovered file in-process and map its entries to corpus records.
Used by the normal in-process driver and by the internal one-file child mode. -/
unsafe def extractOneFileViaFrontend (df : Discover.DiscoveredFile)
    (tagConfig : TagConfig) (opts : CollectOptions)
    : IO (Array ConstRecord) := do
  Frontend.initFrontend
  let importLock : Frontend.ImportLock ← Std.Mutex.new ()
  let r ← Frontend.elaborateFile importLock df
  if r.hasErrors then
    throw <| IO.userError s!"Lean reported errors while elaborating {df.relPath}"
  let entries ← extractFileEntries r opts
  return entries.map fun e => entryToRecord e df.relPath tagConfig

/-- Decode child-process stdout as record JSONL. Shares the extractor's line
format via `Corpus.Artifact` so writer and reader cannot drift. -/
private def parseRecordsJsonl (stdout : String) : Except String (Array ConstRecord) :=
  Artifact.parseJsonl stdout

/-! ## Resumable per-file shards -/

namespace Resume

def formatVersion : String := "corpus-extract-resume.v2"

private def fileHashJson (path : System.FilePath) : IO Json := do
  if (← path.pathExists) then
    return Json.str (← Lake.computeFileHash path).toString
  return Json.null

private def projectSourceHashes (root : System.FilePath) : IO (Array Json) := do
  let files := (← Discover.enumerateLeanFiles root).qsort (·.toString < ·.toString)
  files.mapM fun path => do
    let abs ← IO.FS.realPath path
    return Json.mkObj [
      ("path", Json.str (Discover.relativeTo root abs)),
      ("hash", Json.str (← Lake.computeFileHash abs).toString)
    ]

/-- Fingerprint output-affecting inputs. Any mismatch invalidates staging. -/
def runFingerprint (projectRoot : System.FilePath)
    (configPath? : Option System.FilePath) (opts : CollectOptions)
    (reverseTimeoutMs : Nat) : IO Json := do
  let root ← IO.FS.realPath projectRoot
  let configHash ← match configPath? with
    | some path => fileHashJson path
    | none => pure Json.null
  let executableHash ← fileHashJson (← IO.appPath)
  let leanPath := (← IO.getEnv "LEAN_PATH").getD ""
  return Json.mkObj [
    ("formatVersion", Json.str formatVersion),
    ("projectRoot", Json.str root.toString),
    ("projectSources", Json.arr (← projectSourceHashes root)),
    ("lakefileLean", ← fileHashJson (root / "lakefile.lean")),
    ("lakefileToml", ← fileHashJson (root / "lakefile.toml")),
    ("lakeManifest", ← fileHashJson (root / "lake-manifest.json")),
    ("leanToolchain", ← fileHashJson (root / "lean-toolchain")),
    ("leanGithash", Json.str Lean.githash),
    ("leanPath", Json.str leanPath),
    ("executableHash", executableHash),
    ("configHash", configHash),
    ("includeInternal", Json.bool opts.includeInternal),
    ("includePrivate", Json.bool opts.includePrivate),
    ("reverseElab", Json.bool opts.reverseElab),
    ("reverseClosers", Json.bool opts.reverseClosers),
    ("reverseSkip", Json.arr ((opts.reverseSkip.qsort (· < ·)).map Json.str)),
    ("proofMetrics", Json.bool opts.proofMetrics),
    ("reverseTimeoutMs", Json.num (JsonNumber.fromNat reverseTimeoutMs))
  ]

/-- Fail when output-affecting inputs changed during extraction. -/
def checkRunFingerprint (projectRoot : System.FilePath)
    (configPath? : Option System.FilePath) (opts : CollectOptions)
    (reverseTimeoutMs : Nat) (expected : Json) : IO Unit := do
  let actual ← runFingerprint projectRoot configPath? opts reverseTimeoutMs
  unless actual == expected do
    throw <| IO.userError "extraction inputs changed during the run; staged shards were retained"

/-- Map a source path to a collision-free shard path. -/
def shardPath (shardsDir : System.FilePath) (df : Discover.DiscoveredFile) :
    System.FilePath :=
  (shardsDir / "records" / df.relPath).withExtension "jsonl"

private def shardSourceHashPath (path : System.FilePath) : System.FilePath :=
  path.addExtension "source-hash"

/-- Publish a record shard and source hash via temporary files. -/
def writeShard (shardsDir : System.FilePath) (df : Discover.DiscoveredFile)
    (sourceHash : Lake.Hash) (recs : Array ConstRecord) : IO Unit := do
  let path := shardPath shardsDir df
  let hashPath := shardSourceHashPath path
  let tmp := path.addExtension "tmp"
  let hashTmp := hashPath.addExtension "tmp"
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  let payload := String.join (recs.toList.map (fun r => (Lean.toJson r).compress ++ "\n"))
  IO.FS.writeFile tmp payload
  IO.FS.writeFile hashTmp sourceHash.toString
  IO.FS.rename tmp path
  IO.FS.rename hashTmp hashPath

/-- Return a shard only when it parses and its source hash matches. -/
def readValidShard (shardsDir : System.FilePath) (df : Discover.DiscoveredFile)
    (sourceHash : Lake.Hash)
    : IO (Option (Array ConstRecord)) := do
  let path := shardPath shardsDir df
  let hashPath := shardSourceHashPath path
  unless (← path.pathExists) do return none
  unless (← hashPath.pathExists) do return none
  let storedHash ← try IO.FS.readFile hashPath catch _ => return none
  unless storedHash.trimAscii.toString == sourceHash.toString do return none
  let content ← try IO.FS.readFile path catch _ => return none
  match parseRecordsJsonl content with
  | .ok recs => return some recs
  | .error _ => return none

/-- Reuse staging on a fingerprint match; otherwise initialize it afresh. -/
def prepareShardsDir (outDir : System.FilePath) (resume : Bool) (fp : Json)
    : IO System.FilePath := do
  let shardsDir := outDir / ".shards"
  let fpPath := shardsDir / "run.json"
  let reuse ← do
    if !resume then pure false
    else if !(← fpPath.pathExists) then pure false
    else
      let stored ← try IO.FS.readFile fpPath catch _ => pure ""
      pure (stored.trimAscii.toString == Json.compress fp)
  if reuse then
    IO.eprintln "corpus-extract: --resume: reusing valid shards from a prior run"
  else
    if (← shardsDir.pathExists) then
      if resume then
        IO.eprintln "corpus-extract: --resume: run inputs changed since last run; discarding stale shards"
      IO.FS.removeDirAll shardsDir
    IO.FS.createDirAll shardsDir
    IO.FS.writeFile fpPath (Json.compress fp)
  return shardsDir

end Resume

private inductive IsolatedOutcome where
  | ok       (recs : Array ConstRecord)
  | timedOut
  | failed   (msg : String)

/-- The complete request for one isolated file-extraction child: which file, and the
collection options. Serialized as ONE JSON argument, so parent and child share a
single encoding of the options rather than a hand-written flag writer paired with a
hand-written flag parser. -/
structure ExtractOneRequest where
  sourceFile : System.FilePath
  module     : Name
  relPath    : String
  config     : Option System.FilePath := none
  opts       : CollectOptions := {}
  deriving Inhabited, ToJson, FromJson

/-- The flag that carries an `ExtractOneRequest` to the child. -/
def extractOneFlag : String := "--internal-extract-one"

private def runIsolatedFileChild (df : Discover.DiscoveredFile)
    (opts : CollectOptions)
    (configPath? : Option System.FilePath)
    (timeoutMs : Nat := 0)
    : IO IsolatedOutcome := do
  let exe ← IO.appPath
  let request : ExtractOneRequest := {
    sourceFile := df.absPath, module := df.module, relPath := df.relPath
    config := configPath?, opts }
  let args := #[extractOneFlag, (toJson request).compress]
  let child ← IO.Process.spawn {
    cmd := exe.toString
    args := args
    stdin := .null
    stdout := .piped
    stderr := .inherit
    -- `Child.kill` terminates this process group, including nested work.
    setsid := true
  }
  -- Drain stdout while polling the process deadline.
  let stdoutTask ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let started ← IO.monoMsNow
  match (← ChildProcess.waitWithDeadline child started timeoutMs) with
  | none =>
      let _ ← IO.wait stdoutTask
      return .timedOut
  | some code =>
      let stdout ← IO.ofExcept (← IO.wait stdoutTask)
      if code != 0 then
        return .failed s!"child exited with code {code}"
      match parseRecordsJsonl stdout with
      | .ok recs  => return .ok recs
      | .error e  => return .failed e

/-- Drive every discovered file through a fresh child process, then merge records
in discovery order. This is slower than `extractViaFrontend`, but bounds memory
for large projects because each file's Lean environment dies with its child. -/
unsafe def extractViaFrontendIsolated (projectRoot : System.FilePath)
    (files : Array Discover.DiscoveredFile) (opts : CollectOptions)
    (configPath? : Option System.FilePath := none)
    (maxConcurrent : Nat := Frontend.defaultMaxConcurrent)
    (reverseTimeoutMs : Nat := 0)
    (outDir : System.FilePath := ".") (resume : Bool := false)
    : IO (Array ConstRecord × WorkerRunStats) := do
  let mut recs : Array ConstRecord := #[]
  let mut stats : WorkerRunStats := { filesTotal := files.size }
  let jobs := Nat.max 1 maxConcurrent
  let timeoutMs := if opts.reverseElab then reverseTimeoutMs else 0
  let fp ← Resume.runFingerprint projectRoot configPath? opts reverseTimeoutMs
  let shardsDir ← Resume.prepareShardsDir outDir resume fp
  let runOne (i : Nat) (df : Discover.DiscoveredFile) :
      IO (Discover.DiscoveredFile × Except String (Array ConstRecord)) := do
    let sourceHash ← Lake.computeFileHash df.absPath
    if resume then
      if let some cached ← Resume.readValidShard shardsDir df sourceHash then
        IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} reused shard {df.relPath} ({cached.size} record(s))"
        return (df, .ok cached)
    IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} starting {df.relPath}"
    let r ← runIsolatedFileChild df opts configPath? timeoutMs
    match r with
    | .ok fileRecs =>
        let sourceHashAfter ← Lake.computeFileHash df.absPath
        if sourceHashAfter != sourceHash then
          return (df, .error "source file changed while it was being extracted")
        Resume.writeShard shardsDir df sourceHash fileRecs
        IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} finished {df.relPath} ({fileRecs.size} record(s))"
        return (df, .ok fileRecs)
    | .timedOut =>
        -- Preserve records when reverse elaboration times out.
        IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} timed out {df.relPath} \
          after {timeoutMs}ms; re-running baseline-only (no reverse-elab)"
        let r2 ← runIsolatedFileChild df
          { opts with reverseElab := false, reverseClosers := false } configPath? timeoutMs
        match r2 with
        | .ok fileRecs =>
            let sourceHashAfter ← Lake.computeFileHash df.absPath
            if sourceHashAfter != sourceHash then
              return (df, .error "source file changed while it was being extracted")
            Resume.writeShard shardsDir df sourceHash fileRecs
            IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} recovered {df.relPath} ({fileRecs.size} baseline record(s))"
            return (df, .ok fileRecs)
        | .timedOut =>
            return (df, .error s!"baseline re-run timed out after {timeoutMs}ms")
        | .failed msg =>
            IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} baseline re-run failed {df.relPath}: {msg}"
            return (df, .error msg)
    | .failed msg =>
        IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} failed {df.relPath}: {msg}"
        return (df, .error msg)
  for result in (← batchedMap files jobs runOne) do
    match result with
    | .ok (_, .ok fileRecs) =>
        if fileRecs.isEmpty then
          stats := { stats with filesEmpty := stats.filesEmpty + 1 }
        else
          stats := { stats with filesOk := stats.filesOk + 1 }
        recs := recs ++ fileRecs
    | .ok (_, .error _) =>
        stats := { stats with filesError := stats.filesError + 1 }
    | .error e =>
        stats := { stats with filesError := stats.filesError + 1 }
        IO.eprintln s!"corpus-extract: isolated file extraction task failed: {e}"
  Resume.checkRunFingerprint projectRoot configPath? opts reverseTimeoutMs fp
  return (recs, stats)

/-- Best-effort staging cleanup after a successful run. -/
def cleanupShards (outDir : System.FilePath) : IO Unit := do
  let shardsDir := outDir / ".shards"
  if (← shardsDir.pathExists) then
    try IO.FS.removeDirAll shardsDir catch _ => pure ()

/-- Drive every discovered file through the frontend (in parallel) and collect
`ConstRecord`s. Per-file errors are logged to stderr and skipped (one bad file
never aborts the run). Records keep the `file` field from discovery and `tags`
from `tagConfig`.

`unsafe` because in-process elaboration runs imported modules' interpreted
`initialize` code (see `Frontend.elaborateFile`). -/
unsafe def extractViaFrontend (files : Array Discover.DiscoveredFile)
    (tagConfig : TagConfig) (opts : CollectOptions)
    (jobs : Nat := Frontend.defaultMaxConcurrent)
    : IO (Array ConstRecord × WorkerRunStats) := do
  let (results, stats) ← FileDriver.driveFiles files
    (collect := fun r => do
      let entries ← extractFileEntries r opts
      pure ((), entries))
    (jobs := jobs) (progressLabel := some "file extraction") (rejectFileErrors := true)
  -- Aggregate in discovery order.
  let recs := results.flatMap fun fr =>
    fr.entries.map fun e => entryToRecord e fr.file.relPath tagConfig
  return (recs, stats)

end Corpus
