import Lean
import Corpus.Records
import Corpus.Tags
import Corpus.Discover
import Workers.WorkerPool
import WorkerPlugins.CorpusManifest

/-!
Worker-driven extraction: the THIN-CLIENT half of the corpus extractor.

Instead of importing the project and walking the `Environment` (`Corpus.Extract`),
this drives a pool of `lean --worker` subprocesses — one elaboration per source
file in its TRUE context — and pulls a `$/lean/corpusManifest` back over LSP for
each. Each `CorpusManifestEntry` is mapped to the existing `ConstRecord` JSONL
schema, so the output is byte-comparable to the import-based corpus.

The plugin computes everything that needs an `Environment` (type/value/deps/
premises/axioms/signature/body/proof_script, plus isPrivate/isProtected/
isStructure/ranges and the corpus-eligibility filter); the client only supplies
the `file` path (from discovery) and `tags` (from the local `TagConfig`), and
performs the kind-string mapping.
-/

namespace Corpus

open Lean Lean.Lsp Workers

/-- Resolve the three plugin `.so` paths the worker must load (helpers BEFORE the
plugin — each helper is an undefined `initialize` symbol in the plugin `.so`).

Directory resolution order: `LEAN_EXTRACT_PLUGIN_DIR` env override, else the
sibling `workers` checkout's build dir relative to this exe. Returns the
`forwardArgs` for `WorkerPool.new`. -/
def resolvePluginArgs : IO (Array String) := do
  let dir : System.FilePath ← match (← IO.getEnv "LEAN_EXTRACT_PLUGIN_DIR") with
    | some d => pure ⟨d⟩
    | none   =>
      -- self is .../lean-extract/.lake/build/bin/lean_extract; workers is a sibling.
      let self ← IO.appPath
      let binDir := self.parent.getD "."
      pure (binDir / ".." / ".." / ".." / ".." / "workers" / ".lake" / "build" / "lib" / "lean")
  let ext := if System.Platform.isOSX then "dylib" else "so"
  let common  := dir / s!"workers_WorkerPlugins_Common.{ext}"
  let reverse := dir / s!"workers_WorkerPlugins_ReverseElab.{ext}"
  let plugin  := dir / s!"workers_WorkerPlugins_CorpusManifest.{ext}"
  for p in #[common, reverse, plugin] do
    unless (← p.pathExists) do
      throw <| .userError s!"plugin .so not found: {p}\n\
        Build them: (cd ../workers && lake build WorkerPlugins.CorpusManifest:dynlib \
        WorkerPlugins.ReverseElab:dynlib WorkerPlugins.Common:dynlib)\n\
        or set LEAN_EXTRACT_PLUGIN_DIR."
  return #[s!"--load-dynlib={common}", s!"--load-dynlib={reverse}", s!"--plugin={plugin}"]

/-- Map the plugin's kind label to the corpus schema's kind, applying the
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

/-- Request `$/lean/corpusManifest` from worker `w` and decode it, bounding the
wait by `timeoutMs`. The worker is assumed already elaborated (`waitForDiagnostics`
done). Pure plumbing shared by the baseline and reverse-elab passes. -/
private def requestManifest (w : Worker) (uri : DocumentUri) (reqId : String)
    (includeInternal includePrivate reverseElab : Bool) (timeoutMs : Nat)
    (closers : Bool := false)
    : IO (Except String (Array CorpusManifestEntry)) := do
  let slot ← w.sendRequest reqId "$/lean/corpusManifest"
    ({ textDocument := { uri }, includeInternal, includePrivate, reverseElab, closers }
      : CorpusManifestParams)
  let resp : Except String JsonRpc.Message ←
    try
      let msg ← w.awaitResponse slot timeoutMs
      pure (Except.ok msg)
    catch e => pure (Except.error e.toString)
  match resp with
  | .error e => return .error e
  | .ok (.response _ payload) =>
    match (fromJson? payload : Except String CorpusManifest) with
    | .ok m    => return .ok m.entries
    | .error e => return .error s!"decode: {e}"
  | .ok (.responseError _ _ msg _) => return .error s!"worker error: {msg}"
  | .ok _ => return .error "unexpected message"

/-- Drive ONE file: acquire a worker, wait for elaboration, request the corpus
manifest, decode it. Returns the raw entries or an error string (so the caller
can log-and-continue).

Reverse-elaboration is bounded at the FILE/PROCESS level here, because no
in-process bound is reliable: heartbeats don't track wall time on the worker
path's freshly-elaborated terms, cooperative cancellation doesn't preempt a
single in-flight `isDefEq`, and term size doesn't predict cost (a 112-node proof
was measured at 131s). So when `reverseElab` is requested we make TWO manifest
passes on the same (already-warm) worker:

  1. BASELINE — `reverseElab := false`: fast, always completes, and captures
     every theorem and definition record (just with `proofScript := none`).
  2. ENRICH — `reverseElab := true` under the tight `manifestTimeoutMs`: returns
     the same records WITH proof scripts. If a pathological proof makes the
     worker spin past the deadline, we already hold the baseline, so we drop the
     wedged worker (it cannot be reused) and keep the baseline records — losing
     only the proof SCRIPTS for this one file, never its records.

This costs one extra cheap manifest build per file (the baseline pass), which is
negligible next to reverse-elab; in return no file's records are ever lost to a
reverse-elab timeout. The `reverseProofGuarded` size filter inside the plugin is
the complementary first line of defence: it skips obviously-huge terms so the
enrich pass completes (and the timeout fires) far less often.

Note on `manifestTimeoutMs` granularity: the enrich timeout is per-FILE, so a
single proof that exceeds it discards the proof scripts for ALL theorems in that
file (the records still survive via the baseline). Raising it recovers scripts
only for files whose slowest proof finishes just under the new bound, while
costing the full timeout on every file that still fails — measured, a hard file's
worst proof can take 130s+, so a higher bound buys little coverage for a lot of
wall time. 60s keeps the whole-corpus worker run to ~10min on LeanSQLite. For
COMPLETE proof-script coverage use the import path (`--enumerate import`), which
reverse-elaborates the whole corpus in one pass (~46s) without this per-file
process boundary — it is the recommended route when scripts matter most. -/
def extractFileEntries (pool : WorkerPool) (df : Discover.DiscoveredFile)
    (includeInternal includePrivate reverseElab : Bool) (timeoutMs : Nat := 300000)
    (manifestTimeoutMs : Nat := 60000) (closers : Bool := false)
    : IO (Except String (Array CorpusManifestEntry)) := do
  let text ← IO.FS.readFile df.absPath
  let uri : DocumentUri := s!"file://{df.absPath}"
  let w ← pool.acquire uri text
  match (← w.waitForDiagnostics timeoutMs) with
  | .timeout      => return .error s!"timeout elaborating {df.relPath}"
  | .workerExited => return .error s!"worker exited elaborating {df.relPath}"
  | .done =>
    -- Baseline pass (no reverse-elab): the guaranteed record set.
    let baseline ← requestManifest w uri "corpus/base"
      includeInternal includePrivate (reverseElab := false) timeoutMs
    if !reverseElab then
      return baseline
    -- Enrich pass (reverse-elab, optionally with closers) under the tight
    -- deadline. On timeout/error, fall back to the baseline so records survive.
    match (← requestManifest w uri "corpus/rev"
        includeInternal includePrivate (reverseElab := true) manifestTimeoutMs
        (closers := closers)) with
    | .ok entries => return .ok entries
    | .error e =>
      pool.close uri  -- worker is wedged on a pathological proof; drop it
      match baseline with
      | .ok base =>
        IO.eprintln s!"corpus-extract: reverse-elab timed out for {df.relPath} \
          ({e}); kept {base.size} records without proof scripts"
        return .ok base
      | .error _ => return .error s!"manifest for {df.relPath}: {e}"

/-- Summary of a worker-driven run, for `metadata.json` / stderr reporting. -/
structure WorkerRunStats where
  filesTotal   : Nat := 0
  filesOk      : Nat := 0
  filesEmpty   : Nat := 0  -- elaborated but produced 0 records (header file, or error fallback)
  filesError   : Nat := 0  -- timeout / worker-exited / decode failure
  deriving Inhabited

/-- Drive every discovered file through the pool and collect `ConstRecord`s.
Per-file errors are logged to stderr and skipped (one bad file never aborts the
run). Records keep the `file` field from discovery and `tags` from `tagConfig`. -/
def extractViaWorkers (projectRoot : System.FilePath) (files : Array Discover.DiscoveredFile)
    (tagConfig : TagConfig) (includeInternal includePrivate reverseElab : Bool)
    (reverseClosers : Bool := false)
    : IO (Array ConstRecord × WorkerRunStats) := do
  let forwardArgs ← resolvePluginArgs
  -- `setsidWorkers := false`: this is a batch tool, so its workers should die with it. Without
  -- `setsid` they stay in the parent's process group and a SIGTERM/SIGINT (or the process exiting)
  -- reaps them too, instead of leaving Mathlib-loaded workers pinning CPU as orphans when the run
  -- is interrupted before `closeAll` runs.
  let pool ← WorkerPool.new (maxSize := 4) (forwardArgs := forwardArgs)
    (projectRoot? := some projectRoot) (cache? := none) (setsidWorkers := false)
  let mut recs   : Array ConstRecord := #[]
  let mut stats  : WorkerRunStats := { filesTotal := files.size }
  try
    for df in files do
      match (← extractFileEntries pool df includeInternal includePrivate reverseElab
              (closers := reverseClosers)) with
      | .ok entries =>
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
  finally
    pool.closeAll

end Corpus
