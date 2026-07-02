import Lean
import Corpus.Records
import Corpus.Discover
import Workers.WorkerPool
import WorkerPlugins.GrindInProof

/-!
In-proof grind extraction: the THIN-CLIENT half of the observation-mode collector.

Parallel to `Corpus.GrindExtract`, but drives the `$/lean/grindInProof` request
instead of `$/lean/grindManifest`. For each source file it acquires a worker
(loading the `GrindInProof` plugin), waits for elaboration, then asks the plugin
to walk the file's `InfoTree`s for every `grind` CALL SITE inside a proof,
re-run instrumented grind on each restored subgoal (with the author's hints), and
report the triple + artifacts. Each `GrindInProofEntry` becomes a
`GrindInProofRecord` (adding the `file` path from discovery). The env-wide
`available` hint set is returned per file and merged into one set by the caller.

See `Corpus.GrindExtract` for the shared design rationale (own driver because the
plugin `.so` and per-file budget differ from the corpus fold).
-/

namespace Corpus

open Lean Lean.Lsp Workers

/-- Resolve the plugin `.so` paths for in-proof grind extraction: the shared
`Common` helper AND the `GrindManifest` helper (whose `mkGrindConfig` /
`runGrindCore` the `GrindInProof` plugin reuses — their symbols are undefined in
the `GrindInProof` `.so` and must be resolved by an earlier `--load-dynlib`),
then the `GrindInProof` plugin itself. Order matters: dep libs before the plugin.
Mirrors `resolveGrindPluginArgs`. -/
def resolveGrindInProofPluginArgs : IO (Array String) := do
  let dir : System.FilePath ← match (← IO.getEnv "LEAN_EXTRACT_PLUGIN_DIR") with
    | some d => pure ⟨d⟩
    | none   =>
      let self ← IO.appPath
      let binDir := self.parent.getD "."
      pure (binDir / ".." / ".." / ".." / ".." / "workers" / ".lake" / "build" / "lib" / "lean")
  let ext := if System.Platform.isOSX then "dylib" else "so"
  let common      := dir / s!"workers_WorkerPlugins_Common.{ext}"
  let grindHelper := dir / s!"workers_WorkerPlugins_GrindManifest.{ext}"
  let plugin      := dir / s!"workers_WorkerPlugins_GrindInProof.{ext}"
  for p in #[common, grindHelper, plugin] do
    unless (← p.pathExists) do
      throw <| .userError s!"plugin .so not found: {p}\n\
        Build it: (cd ../workers && lake build WorkerPlugins.GrindInProof:dynlib \
        WorkerPlugins.GrindManifest:dynlib WorkerPlugins.Common:dynlib)\n\
        or set LEAN_EXTRACT_PLUGIN_DIR."
  return #[s!"--load-dynlib={common}", s!"--load-dynlib={grindHelper}",
           s!"--plugin={plugin}"]

/-- Map one `GrindInProofEntry` (a grind call site) to a `GrindInProofRecord`.
`relFile` is the project-relative source path from discovery. -/
def grindInProofEntryToRecord (e : GrindInProofEntry) (relFile : String)
    : GrindInProofRecord :=
  { enclosingTheorem := e.enclosingTheorem
    module           := e.module
    file             := some relFile
    startLine        := e.startLine
    startCol         := e.startCol
    goalType         := e.goalType
    authorHints      := e.authorHints
    authorOnly       := e.authorOnly
    outcome          := e.outcome
    interactive      := e.interactive
    grindOnly        := e.grindOnly
    hasSorry         := e.hasSorry
    activated        := e.activated.toList
    used             := e.used.toList
    coverageGap      := e.coverageGap
    isPrivate        := e.isPrivate }

/-- Request `$/lean/grindInProof` from worker `w` and decode it, bounding the
wait by `timeoutMs`. Returns the `available` hint set and the entries, or an
error string. The worker is assumed already elaborated. -/
private def requestGrindInProof (w : Worker) (uri : DocumentUri) (reqId : String)
    (includePrivate : Bool) (grindDeadlineMs : Nat) (timeoutMs : Nat)
    : IO (Except String (Array String × Array GrindInProofEntry)) := do
  let slot ← w.sendRequest reqId "$/lean/grindInProof"
    ({ textDocument := { uri }, includePrivate, grindDeadlineMs } : GrindInProofParams)
  let resp : Except String JsonRpc.Message ←
    try
      let msg ← w.awaitResponse slot timeoutMs
      pure (Except.ok msg)
    catch e => pure (Except.error e.toString)
  match resp with
  | .error e => return .error e
  | .ok (.response _ payload) =>
    match (fromJson? payload : Except String GrindInProof) with
    | .ok m    => return .ok (m.available, m.entries)
    | .error e => return .error s!"decode: {e}"
  | .ok (.responseError _ _ msg _) => return .error s!"worker error: {msg}"
  | .ok _ => return .error "unexpected message"

/-- Drive ONE file: acquire a worker, wait for elaboration, request the in-proof
grind data, decode it. Returns the file's `available` hint set and its entries,
or an error string (so the caller can log-and-continue). The plugin bounds its
own per-file walk with `grindDeadlineMs` (80% of the LSP `timeoutMs`, tail-shed
to `deadline_skipped`); if the worker wedges past the timeout we drop it and
report an error for the file. -/
def extractGrindInProofFile (pool : WorkerPool) (df : Discover.DiscoveredFile)
    (includePrivate : Bool) (timeoutMs : Nat := 600000)
    : IO (Except String (Array String × Array GrindInProofEntry)) := do
  let text ← IO.FS.readFile df.absPath
  let uri : DocumentUri := s!"file://{df.absPath}"
  let w ← pool.acquire uri text
  match (← w.waitForDiagnostics timeoutMs) with
  | .timeout      => return .error s!"timeout elaborating {df.relPath}"
  | .workerExited => return .error s!"worker exited elaborating {df.relPath}"
  | .done =>
    let grindDeadlineMs := timeoutMs * 4 / 5
    match (← requestGrindInProof w uri "grind/inproof"
        includePrivate grindDeadlineMs timeoutMs) with
    | .ok result => return .ok result
    | .error e =>
      pool.close uri  -- worker may be wedged on a pathological grind run; drop it
      return .error s!"grind-in-proof for {df.relPath}: {e}"

/-- Summary of an in-proof grind-extraction run. File-level counters plus
per-call-site outcome counts. -/
structure GrindInProofRunStats where
  filesTotal   : Nat := 0
  filesOk      : Nat := 0
  filesEmpty   : Nat := 0  -- elaborated but produced 0 grind call sites
  filesError   : Nat := 0
  closed       : Nat := 0  -- call sites grind closed
  stuck        : Nat := 0  -- grind ran but could not close
  errored      : Nat := 0  -- grind threw / site skipped
  skipped      : Nat := 0  -- past the per-file deadline
  deriving Inhabited

/-- Drive every discovered file through the pool and collect
`GrindInProofRecord`s plus the merged env-wide `available` hint set. Per-file
errors are logged to stderr and skipped (one bad file never aborts the run). -/
def extractGrindInProofViaWorkers (projectRoot : System.FilePath)
    (files : Array Discover.DiscoveredFile) (includePrivate : Bool)
    : IO (Array GrindInProofRecord × Array String × GrindInProofRunStats) := do
  let forwardArgs ← resolveGrindInProofPluginArgs
  let pool ← WorkerPool.new (maxSize := 4) (forwardArgs := forwardArgs)
    (projectRoot? := some projectRoot) (cache? := none) (setsidWorkers := false)
  let mut recs      : Array GrindInProofRecord := #[]
  let mut available : Std.HashSet String := {}
  let mut stats     : GrindInProofRunStats := { filesTotal := files.size }
  try
    for df in files do
      match (← extractGrindInProofFile pool df includePrivate) with
      | .ok (avail, entries) =>
        for a in avail do
          available := available.insert a
        if entries.isEmpty then
          stats := { stats with filesEmpty := stats.filesEmpty + 1 }
        else
          stats := { stats with filesOk := stats.filesOk + 1 }
        for e in entries do
          recs := recs.push (grindInProofEntryToRecord e df.relPath)
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
