import Lean
import Corpus.Records
import Corpus.Tags
import Corpus.Discover
import Corpus.Frontend
import Corpus.CorpusManifest
import Lake.Build.Trace

/-!
Frontend-driven corpus extraction.

Historically this drove a pool of `lean --worker` subprocesses and pulled a
`$/lean/corpusManifest` back over LSP per file. It now drives Lean's frontend
directly via `Corpus.Frontend`. Isolated mode runs one frontend process per file;
the optional shared-process mode uses `elaborateFiles`.

Each `CorpusManifestEntry` is mapped to the existing `ConstRecord` JSONL schema,
so the output is byte-comparable to the previous worker-driven corpus. The client
supplies the `file` path (from discovery) and `tags` (from the local `TagConfig`)
and performs the kind-string mapping; the collector computes everything that needs
an `Environment`.

`extractViaFrontend` is the frontend-driven glob path, as opposed to the legacy
`--enumerate import` walk.
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
    tags        := tagConfig.matchTags e.module }

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
def extractFileEntries (r : Frontend.ElabResult)
    (includeInternal includePrivate reverseElab : Bool)
    (manifestTimeoutMs : Nat := 60000) (closers : Bool := false)
    (reverseSkip : Array String := #[])
    : IO (Array CorpusManifestEntry) := do
  -- Baseline pass (no reverse-elab): the guaranteed record set.
  let baseline ← corpusManifestCore r includeInternal includePrivate
    (reverseElab := false) (closers := false)
  if !reverseElab then
    return baseline
  -- Enrich pass (reverse-elab, optionally with closers) under the fold's internal
  -- wall-clock budget (80% of the per-file timeout, headroom for the rest). On any
  -- failure we fall back to the baseline so records survive.
  let reverseDeadlineMs := manifestTimeoutMs * 4 / 5
  try
    corpusManifestCore r includeInternal includePrivate
      (reverseElab := true) (closers := closers) (reverseDeadlineMs := reverseDeadlineMs)
      (reverseSkip := reverseSkip)
  catch e =>
    IO.eprintln s!"corpus-extract: reverse-elab failed for {r.file.relPath} \
      ({e.toString}); kept {baseline.size} records without proof scripts"
    return baseline

/-- Summary of an extraction run, for `metadata.json` / stderr reporting. -/
structure WorkerRunStats where
  filesTotal   : Nat := 0
  filesOk      : Nat := 0
  filesEmpty   : Nat := 0  -- elaborated but produced 0 records (header file, or error fallback)
  filesError   : Nat := 0  -- elaboration failed
  deriving Inhabited


/-- Extract one discovered file in-process and map its entries to corpus records.
Used by the normal in-process driver and by the internal one-file child mode. -/
unsafe def extractOneFileViaFrontend (projectRoot : System.FilePath)
    (df : Discover.DiscoveredFile) (tagConfig : TagConfig)
    (includeInternal includePrivate reverseElab : Bool)
    (reverseClosers : Bool := false) (reverseSkip : Array String := #[])
    : IO (Array ConstRecord) := do
  let _ := projectRoot
  Frontend.initFrontend
  let importLock : Frontend.ImportLock ← Std.Mutex.new ()
  let r ← Frontend.elaborateFile importLock df
  if r.hasErrors then
    throw <| IO.userError s!"Lean reported errors while elaborating {df.relPath}"
  let entries ← extractFileEntries r includeInternal includePrivate reverseElab
    (closers := reverseClosers) (reverseSkip := reverseSkip)
  return entries.map fun e => entryToRecord e df.relPath tagConfig

private def parseRecordsJsonl (stdout : String) : Except String (Array ConstRecord) := do
  let mut out : Array ConstRecord := #[]
  for line in stdout.splitOn "\n" do
    let line := line.trimAscii.toString
    if line.isEmpty then
      continue
    let json ← Json.parse line
    let rec ← (Lean.fromJson? json : Except String ConstRecord)
    out := out.push rec
  return out

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
    let rel0 := (abs.toString.dropPrefix root.toString).copy
    let rel := ((rel0.dropPrefix "/").copy.dropPrefix "\\").copy
    return Json.mkObj [
      ("path", Json.str rel),
      ("hash", Json.str (← Lake.computeFileHash abs).toString)
    ]

/-- Fingerprint output-affecting inputs. Any mismatch invalidates staging. -/
def runFingerprint (projectRoot : System.FilePath)
    (configPath? : Option System.FilePath)
    (includeInternal includePrivate reverseElab reverseClosers : Bool)
    (reverseSkip : Array String) (reverseTimeoutMs : Nat) : IO Json := do
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
    ("includeInternal", Json.bool includeInternal),
    ("includePrivate", Json.bool includePrivate),
    ("reverseElab", Json.bool reverseElab),
    ("reverseClosers", Json.bool reverseClosers),
    ("reverseSkip", Json.arr ((reverseSkip.qsort (· < ·)).map Json.str)),
    ("reverseTimeoutMs", Json.num (JsonNumber.fromNat reverseTimeoutMs))
  ]

/-- Fail when output-affecting inputs changed during extraction. -/
def checkRunFingerprint (projectRoot : System.FilePath)
    (configPath? : Option System.FilePath)
    (includeInternal includePrivate reverseElab reverseClosers : Bool)
    (reverseSkip : Array String) (reverseTimeoutMs : Nat) (expected : Json) : IO Unit := do
  let actual ← runFingerprint projectRoot configPath? includeInternal includePrivate
    reverseElab reverseClosers reverseSkip reverseTimeoutMs
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

/-- Wait for a child, killing it when a nonzero timeout expires. -/
private partial def waitFileChildDeadline {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg) (started timeoutMs : Nat) : IO (Option UInt32) := do
  match (← child.tryWait) with
  | some code => return some code
  | none =>
      if timeoutMs > 0 && (← IO.monoMsNow) - started ≥ timeoutMs then
        try child.kill catch _ => pure ()
        let _ ← child.wait
        return none
      IO.sleep (100 : UInt32)
      waitFileChildDeadline child started timeoutMs

private def runIsolatedFileChild (df : Discover.DiscoveredFile)
    (includeInternal includePrivate reverseElab reverseClosers : Bool)
    (configPath? : Option System.FilePath) (reverseSkip : Array String := #[])
    (timeoutMs : Nat := 0)
    : IO IsolatedOutcome := do
  let exe ← IO.appPath
  let mut args := #[
    "--internal-extract-one",
    "--source-file", df.absPath.toString,
    "--module", df.module.toString,
    "--rel-path", df.relPath
  ]
  if includeInternal then
    args := args.push "--include-internal"
  if !includePrivate then
    args := args.push "--no-private"
  if reverseElab then
    args := args.push "--reverse-elab"
  if reverseClosers then
    args := args.push "--closers"
  for decl in reverseSkip do
    args := args ++ #["--skip-reverse", decl]
  if let some path := configPath? then
    args := args ++ #["--config", path.toString]
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
  match (← waitFileChildDeadline child started timeoutMs) with
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
    (files : Array Discover.DiscoveredFile)
    (tagConfig : TagConfig) (includeInternal includePrivate reverseElab : Bool)
    (reverseClosers : Bool := false) (configPath? : Option System.FilePath := none)
    (reverseSkip : Array String := #[])
    (maxConcurrent : Nat := Frontend.defaultMaxConcurrent)
    (reverseTimeoutMs : Nat := 0)
    (outDir : System.FilePath := ".") (resume : Bool := false)
    : IO (Array ConstRecord × WorkerRunStats) := do
  let _ := tagConfig
  let mut recs : Array ConstRecord := #[]
  let mut stats : WorkerRunStats := { filesTotal := files.size }
  let jobs := Nat.max 1 maxConcurrent
  let timeoutMs := if reverseElab then reverseTimeoutMs else 0
  let fp ← Resume.runFingerprint projectRoot configPath? includeInternal includePrivate
    reverseElab reverseClosers reverseSkip reverseTimeoutMs
  let shardsDir ← Resume.prepareShardsDir outDir resume fp
  let runOne (i : Nat) (df : Discover.DiscoveredFile) :
      IO (Discover.DiscoveredFile × Except String (Array ConstRecord)) := do
    let sourceHash ← Lake.computeFileHash df.absPath
    if resume then
      if let some cached ← Resume.readValidShard shardsDir df sourceHash then
        IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} reused shard {df.relPath} ({cached.size} record(s))"
        return (df, .ok cached)
    IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} starting {df.relPath}"
    let r ← runIsolatedFileChild df includeInternal includePrivate reverseElab reverseClosers configPath? reverseSkip timeoutMs
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
        let r2 ← runIsolatedFileChild df includeInternal includePrivate
          (reverseElab := false) (reverseClosers := false) configPath? reverseSkip timeoutMs
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
  let mut i := 0
  while i < files.size do
    let stop := Nat.min files.size (i + jobs)
    let batch := files.extract i stop
    let mut tasks : Array (Task (Except IO.Error (Discover.DiscoveredFile × Except String (Array ConstRecord)))) := #[]
    for h : j in [0:batch.size] do
      let idx := i + j
      let df := batch[j]
      tasks := tasks.push (← IO.asTask (prio := .dedicated) (runOne idx df))
    let results ← tasks.mapM fun t => IO.wait t
    for result in results do
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
    i := stop
  Resume.checkRunFingerprint projectRoot configPath? includeInternal includePrivate
    reverseElab reverseClosers reverseSkip reverseTimeoutMs fp
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
unsafe def extractViaFrontend (projectRoot : System.FilePath)
    (files : Array Discover.DiscoveredFile)
    (tagConfig : TagConfig) (includeInternal includePrivate reverseElab : Bool)
    (reverseClosers : Bool := false)
    (reverseSkip : Array String := #[])
    (jobs : Nat := Frontend.defaultMaxConcurrent)
    : IO (Array ConstRecord × WorkerRunStats) := do
  let _ := projectRoot  -- retained in the signature for parity; discovery already resolved paths
  Frontend.initFrontend
  let startedRef ← IO.mkRef 0
  let finishedRef ← IO.mkRef 0
  -- Elaborate each file and run the corpus collector, all on the file's own thread.
  let results ← Frontend.elaborateFiles files (fun importLock df => do
    let started ← startedRef.modifyGet fun n => (n + 1, n + 1)
    IO.eprintln s!"corpus-extract: file extraction {started}/{files.size} starting {df.relPath}"
    try
      let r ← Frontend.elaborateFile importLock df
      if r.hasErrors then
        throw <| IO.userError s!"Lean reported errors while elaborating {df.relPath}"
      let entries ← extractFileEntries r includeInternal includePrivate reverseElab
        (closers := reverseClosers) (reverseSkip := reverseSkip)
      let finished ← finishedRef.modifyGet fun n => (n + 1, n + 1)
      IO.eprintln s!"corpus-extract: file extraction {finished}/{files.size} finished {df.relPath} ({entries.size} record(s))"
      pure (df, entries)
    catch e =>
      let finished ← finishedRef.modifyGet fun n => (n + 1, n + 1)
      IO.eprintln s!"corpus-extract: file extraction {finished}/{files.size} failed {df.relPath}: {e.toString}"
      throw e) (maxConcurrent := jobs)
  -- Aggregate in discovery order.
  let mut recs   : Array ConstRecord := #[]
  let mut stats  : WorkerRunStats := { filesTotal := files.size }
  for res in results do
    match res with
    | .ok (df, entries) =>
      if entries.isEmpty then
        stats := { stats with filesEmpty := stats.filesEmpty + 1 }
      else
        stats := { stats with filesOk := stats.filesOk + 1 }
      for e in entries do
        recs := recs.push (entryToRecord e df.relPath tagConfig)
    | .error msg =>
      stats := { stats with filesError := stats.filesError + 1 }
      IO.eprintln s!"corpus-extract: {msg}"
  return (recs, stats)

end Corpus
