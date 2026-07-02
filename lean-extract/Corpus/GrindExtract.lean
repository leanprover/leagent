import Lean
import Corpus.Records
import Corpus.Discover
import Workers.WorkerPool
import WorkerPlugins.GrindManifest

/-!
Grind-manifest extraction: the THIN-CLIENT half of the AlphaGrind data collector.

Parallel to `Corpus.WorkerExtract`, but drives the `$/lean/grindManifest` request
instead of `$/lean/corpusManifest`. For each source file it acquires a worker
(loading the `GrindManifest` plugin), waits for elaboration, then asks the plugin
to RE-PROVE every theorem in the file with `grind`'s default strategy and report
what grind did. Each `GrindManifestEntry` becomes a `GrindGoalRecord` (adding the
`file` path from discovery). The file-level `available` hint set is returned per
file and merged into a single env-wide set by the caller.

Why its own driver rather than an extra pass in `WorkerExtract`: the grind plugin
loads a DIFFERENT `.so` (`GrindManifest`, not `CorpusManifest`), so the worker
pool's `forwardArgs` differ; and grind re-proving is far more expensive than the
corpus fold, so it gets its own per-file wall-clock budget.
-/

namespace Corpus

open Lean Lean.Lsp Workers

/-- Resolve the plugin `.so` paths the worker must load for grind extraction:
the shared `Common` helper (undefined `initialize` symbol in the plugin `.so`),
then the `GrindManifest` plugin itself. Mirrors `WorkerExtract.resolvePluginArgs`
but for the grind plugin. Directory resolution: `LEAN_EXTRACT_PLUGIN_DIR` env
override, else the sibling `workers` build dir relative to this exe. -/
def resolveGrindPluginArgs : IO (Array String) := do
  let dir : System.FilePath ← match (← IO.getEnv "LEAN_EXTRACT_PLUGIN_DIR") with
    | some d => pure ⟨d⟩
    | none   =>
      let self ← IO.appPath
      let binDir := self.parent.getD "."
      pure (binDir / ".." / ".." / ".." / ".." / "workers" / ".lake" / "build" / "lib" / "lean")
  let ext := if System.Platform.isOSX then "dylib" else "so"
  let common := dir / s!"workers_WorkerPlugins_Common.{ext}"
  let plugin := dir / s!"workers_WorkerPlugins_GrindManifest.{ext}"
  for p in #[common, plugin] do
    unless (← p.pathExists) do
      throw <| .userError s!"plugin .so not found: {p}\n\
        Build it: (cd ../workers && lake build WorkerPlugins.GrindManifest:dynlib \
        WorkerPlugins.Common:dynlib)\n\
        or set LEAN_EXTRACT_PLUGIN_DIR."
  return #[s!"--load-dynlib={common}", s!"--plugin={plugin}"]

/-- Map one `GrindManifestEntry` to a `GrindGoalRecord`. `relFile` is the
project-relative source path from discovery. `sourceUsesGrind` is a best-effort
flag supplied by the caller (currently always `false`; per-theorem source mining
is a later pass). -/
def grindEntryToRecord (e : GrindManifestEntry) (relFile : String)
    (sourceUsesGrind : Bool := false) : GrindGoalRecord :=
  { name            := e.name
    module          := e.module
    file            := some relFile
    startLine       := e.startLine
    goalType        := e.goalType
    outcome         := e.outcome
    interactive     := e.interactive
    grindOnly       := e.grindOnly
    hasSorry        := e.hasSorry
    activated       := e.activated.toList
    used            := e.used.toList
    coverageGap     := e.coverageGap
    isPrivate       := e.isPrivate
    sourceUsesGrind := sourceUsesGrind }

/-- Request `$/lean/grindManifest` from worker `w` and decode it, bounding the
wait by `timeoutMs`. Returns the `available` hint set and the entries, or an
error string. The worker is assumed already elaborated. -/
private def requestGrindManifest (w : Worker) (uri : DocumentUri) (reqId : String)
    (includePrivate : Bool) (grindDeadlineMs : Nat) (timeoutMs : Nat)
    : IO (Except String (Array String × Array GrindManifestEntry)) := do
  let slot ← w.sendRequest reqId "$/lean/grindManifest"
    ({ textDocument := { uri }, includePrivate, grindDeadlineMs } : GrindManifestParams)
  let resp : Except String JsonRpc.Message ←
    try
      let msg ← w.awaitResponse slot timeoutMs
      pure (Except.ok msg)
    catch e => pure (Except.error e.toString)
  match resp with
  | .error e => return .error e
  | .ok (.response _ payload) =>
    match (fromJson? payload : Except String GrindManifest) with
    | .ok m    => return .ok (m.available, m.entries)
    | .error e => return .error s!"decode: {e}"
  | .ok (.responseError _ _ msg _) => return .error s!"worker error: {msg}"
  | .ok _ => return .error "unexpected message"

/-- Drive ONE file: acquire a worker, wait for elaboration, request the grind
manifest, decode it. Returns the file's `available` hint set and its entries, or
an error string (so the caller can log-and-continue).

The plugin bounds its own per-file grind fold with `grindDeadlineMs` (measured
inside the worker: cheap-first, tail-shed to `deadline_skipped`). We set it to
80% of the LSP `timeoutMs` so the response returns before the request would be
killed mid-flight; the 20% headroom covers serialization + transport. If the
worker wedges past the timeout anyway, we drop it and report an error for the
file (its records are lost — unlike the corpus path there is no cheap baseline
to fall back on, since every grind record is itself expensive). -/
def extractGrindFile (pool : WorkerPool) (df : Discover.DiscoveredFile)
    (includePrivate : Bool) (timeoutMs : Nat := 600000)
    : IO (Except String (Array String × Array GrindManifestEntry)) := do
  let text ← IO.FS.readFile df.absPath
  let uri : DocumentUri := s!"file://{df.absPath}"
  let w ← pool.acquire uri text
  match (← w.waitForDiagnostics timeoutMs) with
  | .timeout      => return .error s!"timeout elaborating {df.relPath}"
  | .workerExited => return .error s!"worker exited elaborating {df.relPath}"
  | .done =>
    let grindDeadlineMs := timeoutMs * 4 / 5
    match (← requestGrindManifest w uri "grind/manifest"
        includePrivate grindDeadlineMs timeoutMs) with
    | .ok result => return .ok result
    | .error e =>
      pool.close uri  -- worker may be wedged on a pathological grind run; drop it
      return .error s!"grind manifest for {df.relPath}: {e}"

/-- Summary of a grind-extraction run. -/
structure GrindRunStats where
  filesTotal   : Nat := 0
  filesOk      : Nat := 0
  filesEmpty   : Nat := 0  -- elaborated but produced 0 grind records
  filesError   : Nat := 0
  closed       : Nat := 0  -- theorems grind closed
  stuck        : Nat := 0  -- grind ran but could not close
  errored      : Nat := 0  -- grind threw
  skipped      : Nat := 0  -- past the per-file deadline
  deriving Inhabited

/-- Drive every discovered file through the pool and collect `GrindGoalRecord`s
plus the merged env-wide `available` hint set. Per-file errors are logged to
stderr and skipped (one bad file never aborts the run). -/
def extractGrindViaWorkers (projectRoot : System.FilePath)
    (files : Array Discover.DiscoveredFile) (includePrivate : Bool)
    : IO (Array GrindGoalRecord × Array String × GrindRunStats) := do
  let forwardArgs ← resolveGrindPluginArgs
  let pool ← WorkerPool.new (maxSize := 4) (forwardArgs := forwardArgs)
    (projectRoot? := some projectRoot) (cache? := none) (setsidWorkers := false)
  let mut recs      : Array GrindGoalRecord := #[]
  let mut available : Std.HashSet String := {}
  let mut stats     : GrindRunStats := { filesTotal := files.size }
  try
    for df in files do
      match (← extractGrindFile pool df includePrivate) with
      | .ok (avail, entries) =>
        for a in avail do
          available := available.insert a
        if entries.isEmpty then
          stats := { stats with filesEmpty := stats.filesEmpty + 1 }
        else
          stats := { stats with filesOk := stats.filesOk + 1 }
        for e in entries do
          recs := recs.push (grindEntryToRecord e df.relPath)
          stats := match e.outcome with
            | "closed"           => { stats with closed  := stats.closed + 1 }
            | "stuck"            => { stats with stuck   := stats.stuck + 1 }
            | "deadline_skipped" => { stats with skipped := stats.skipped + 1 }
            | _                  => { stats with errored := stats.errored + 1 }
      | .error msg =>
        stats := { stats with filesError := stats.filesError + 1 }
        IO.eprintln s!"corpus-extract: {msg}"
    let availArr := (available.toList.mergeSort (· < ·)).toArray
    return (recs, availArr, stats)
  finally
    pool.closeAll

end Corpus
