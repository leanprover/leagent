import Lean
import Corpus.Records
import Corpus.Tags
import Corpus.Discover
import Corpus.Frontend
import Corpus.CorpusManifest

/-!
Frontend-driven corpus extraction: the in-process successor to the worker driver.

Historically this drove a pool of `lean --worker` subprocesses and pulled a
`$/lean/corpusManifest` back over LSP per file. It now drives Lean's frontend
directly, in-process, via `Corpus.Frontend`: each discovered file is elaborated
in its TRUE context (`elaborateFile`) and the same corpus collector
(`corpusManifestCore`) is folded over the resulting environment. Files are
processed in parallel on dedicated threads (`elaborateFiles`), with the
header/import phase serialized behind a single lock (see `Corpus.Frontend`).

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

private def runIsolatedFileChild (df : Discover.DiscoveredFile)
    (includeInternal includePrivate reverseElab reverseClosers : Bool)
    (configPath? : Option System.FilePath) (reverseSkip : Array String := #[])
    : IO (Except String (Array ConstRecord)) := do
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
  }
  let stdout ← child.stdout.readToEnd
  let code ← child.wait
  if code != 0 then
    return .error s!"child exited with code {code}"
  return parseRecordsJsonl stdout

/-- Drive every discovered file through a fresh child process, then merge records
in discovery order. This is slower than `extractViaFrontend`, but bounds memory
for large projects because each file's Lean environment dies with its child. -/
unsafe def extractViaFrontendIsolated (projectRoot : System.FilePath)
    (files : Array Discover.DiscoveredFile)
    (tagConfig : TagConfig) (includeInternal includePrivate reverseElab : Bool)
    (reverseClosers : Bool := false) (configPath? : Option System.FilePath := none)
    (reverseSkip : Array String := #[])
    (maxConcurrent : Nat := Frontend.defaultMaxConcurrent)
    : IO (Array ConstRecord × WorkerRunStats) := do
  let _ := projectRoot
  let _ := tagConfig
  let mut recs : Array ConstRecord := #[]
  let mut stats : WorkerRunStats := { filesTotal := files.size }
  let jobs := Nat.max 1 maxConcurrent
  let runOne (i : Nat) (df : Discover.DiscoveredFile) :
      IO (Discover.DiscoveredFile × Except String (Array ConstRecord)) := do
    IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} starting {df.relPath}"
    let r ← runIsolatedFileChild df includeInternal includePrivate reverseElab reverseClosers configPath? reverseSkip
    match r with
    | .ok fileRecs =>
        IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} finished {df.relPath} ({fileRecs.size} record(s))"
    | .error msg =>
        IO.eprintln s!"corpus-extract: isolated file extraction {i+1}/{files.size} failed {df.relPath}: {msg}"
    return (df, r)
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
  return (recs, stats)

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
