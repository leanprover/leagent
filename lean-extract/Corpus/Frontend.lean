/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean
import Std.Sync.Mutex
import Corpus.Discover

/-!
In-process frontend driver: the substrate that REPLACES the `lean --worker`
subprocess + LSP model.

Instead of spawning a worker per file and pulling a custom `$/lean/…Manifest`
request back over LSP, we drive Lean's own frontend directly, in this process,
and hand the resulting `(Environment, per-command Syntax, InfoTrees)` to the same
pure `CoreM` collectors the plugins used to run worker-side. Concretely:

  parseHeader  →  processHeader (import the file's deps)  →  IO.processCommands

`IO.processCommands` runs the command loop SYNCHRONOUSLY (`Elab.async` defaults
to `false`, and — unlike `runFrontend` — we never set `internal.cmdlineSnapshots`,
so the full per-command state survives). Its result `Frontend.State` carries
exactly the three things the plugins read from `doc.cmdSnaps`/`doc.meta.text`:

  * `commandState.env`            — the post-elaboration environment
  * `commandState.infoState.trees`— the InfoTrees (grind-in-proof walks these)
  * `commands : Array Syntax`     — per-command parsed syntax (signature/body)

## Why an import lock

`importModules (loadExts := true)` — which `processHeader` always uses — updates
UNSYNCHRONIZED process-global refs (`importingRef`/`runInitializersRef`, the env-
extension/attribute registries) via `Lean.withImporting`. Lean's own source is
explicit that only ONE thread may be inside that region at a time. So when we run
files in parallel we first warm up the registry by importing discovered external
header imports once, single-threaded, then serialize each file's header/import
phase behind one process-wide mutex. The per-command elaboration (`IO.processCommands`)
— which touches only the per-file `Environment` value and per-file monad state —
runs OUTSIDE the lock, in parallel.

`withImporting`'s `finally` unconditionally resets `runInitializersRef := false`,
so `enableInitializersExecution` must be re-run INSIDE the lock before EVERY
`processHeader`, not once at startup — otherwise the 2nd+ file's import throws
"enableInitializersExecution must be run before importModules (loadExts := true)".
-/

namespace Corpus.Frontend

open Lean Lean.Elab

/-- The result of elaborating one source file in-process: everything the corpus /
grind collectors need. Mirrors what a worker returned via `handleSnapshotRequest*`
(the last snapshot's environment, the file source, the per-command `Syntax`, and
the InfoTrees), but obtained without a subprocess or LSP round-trip. -/
structure ElabResult where
  /-- The discovered file this came from (absolute path, module `Name`, rel path). -/
  file    : Discover.DiscoveredFile
  /-- Post-elaboration environment (final command state). -/
  env     : Environment
  /-- Full source text (for source-span reconstruction of signature/body). -/
  source  : String
  /-- Per-command parsed `Syntax`, in file order — one entry per top-level command
  AFTER the header (the header is consumed by `parseHeader` before the command loop,
  so it is not included here). This is the array `CorpusManifest`'s
  `buildSourceMap`/`buildSimpArgMap` walk (they select `Command.declaration` nodes;
  a stray non-declaration command is simply skipped). -/
  commands : Array Syntax
  /-- InfoTrees for the file (one per top-level command). `GrindInProof` folds these
  for `grind` tactic call sites. -/
  trees   : PersistentArray Elab.InfoTree
  /-- Whether parsing, imports, or command elaboration reported an error. -/
  hasErrors : Bool

/-- Process-wide serialization of the header/import phase. One per run; shared by
every parallel file task. See the module docstring for why import must be single-
threaded even though command elaboration is not. -/
abbrev ImportLock := Std.Mutex Unit

/-- One-time process setup: make imports discoverable. Call ONCE at startup on the
main thread, before spawning any file task. `enableInitializersExecution` is NOT
done here — it must be re-run inside the import lock before each `processHeader`
(see `elaborateFile`), because `withImporting` resets its flag after every import. -/
def initFrontend : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)

/-- Elaborate one file fully in-process and return everything the collectors need.

The header/import phase runs inside `importLock` (serialized across all parallel
tasks); the per-command elaboration runs outside it (parallel-safe: it touches only
the per-file environment value + monad state). On a header import error we still
return an `ElabResult` over whatever environment `processHeaderCore` produced
(possibly empty) — matching the worker path, where a file that fails to elaborate
its imports simply yields no records rather than aborting the run. Genuine
exceptions propagate to the caller (`elaborateFiles*` catches them per file).

`unsafe` because `enableInitializersExecution` is `unsafe` (it runs imported
modules' interpreted `initialize`/`@[init]` code — the same reason the legacy
import path's `runCli` is `unsafe`). -/
unsafe def elaborateFile (importLock : ImportLock) (df : Discover.DiscoveredFile)
    : IO ElabResult := do
  let source ← IO.FS.readFile df.absPath
  let opts : Options := {}
  let inputCtx := Parser.mkInputContext source df.absPath.toString
  -- Header parse is pure (its own throwaway env), so it needs no lock.
  let (header, parserState, headerMsgs) ← Parser.parseHeader inputCtx
  -- SERIALIZE the import phase. `enableInitializersExecution` must be inside the
  -- lock and before each import: `withImporting`'s finally resets the flag, so a
  -- prior file's import would otherwise leave it false and this import would throw.
  let (env, messages) ← importLock.atomically do
    Lean.enableInitializersExecution
    processHeader (header := header) (opts := opts) (messages := headerMsgs)
      (inputCtx := inputCtx) (trustLevel := 1024) (mainModule := df.module)
  -- Command elaboration runs OUTSIDE the lock (parallel-safe). `Elab.async` is
  -- false by default (`opts` is empty), so this is synchronous and the returned
  -- command state is COMPLETE.
  --
  -- DO NOT set `Elab.async := true` here. `IO.processCommands` /
  -- `processCommandsIncrementally` read the env from `resultSnap.cmdState` and info
  -- trees from the per-command snapshots, but they do NOT drain
  -- `Command.State.snapshotTasks` — which under async is where `addDecl`'s kernel
  -- check, `compileDecls`, theorem-body elaboration, and linters are deferred
  -- (see core `CoreM.lean:35` async docstring; `runFrontend` opts into async only
  -- because it separately drains `snaps`). Async here would risk a nondeterministic,
  -- INCOMPLETE env / info-tree set (far worse than any naming difference). The sync
  -- path is also deterministic (byte-identical across runs); the only divergence
  -- from the legacy `lean --worker` corpus — which elaborated async — is the
  -- attribution/numbering of compiler auxiliaries (`match_*`/`_proof_*`/`_uniq.*`),
  -- since async forks the name generators per task. No real declaration differs.
  let cmdState := Command.mkState env messages opts
  let s ← IO.processCommands inputCtx parserState cmdState
  return {
    file     := df
    env      := s.commandState.env
    source
    commands := s.commands
    trees    := s.commandState.infoState.trees
    hasErrors := s.commandState.messages.hasErrors
  }

/-- Run a `CoreM` collector over an `ElabResult`'s environment, in a `Core` context
carrying the file's real name + `FileMap` (so `FileMap.toPosition` /
`findDeclarationRanges?` line-cols line up with the source) and `maxHeartbeats := 0`
(the batch tool walks a whole file in one action; per-proof cost is bounded locally
inside the collectors). This is the in-process replacement for the worker's
`RequestM.runCoreM last (…)` — same idea (run the collector in the post-elaboration
environment), without the snapshot/LSP machinery. -/
def runCollectorOn {α} (r : ElabResult) (collect : CoreM α) : IO α := do
  let coreCtx : Core.Context := {
    fileName := r.file.absPath.toString
    fileMap  := r.source.toFileMap
    maxHeartbeats := 0
  }
  let coreSt : Core.State := { env := r.env }
  -- `CoreM.toIO` already unwraps the `Except`/`Exception` into `IO` (throwing a
  -- `userError` on a Lean exception), so we only discard the final `Core.State`.
  let (a, _) ← collect.toIO coreCtx coreSt
  return a

/-- Default to sequential execution unless the caller opts into `--jobs`.
Parallel execution is available after `warmupImportRegistry`, but `1` remains the
least surprising default for memory use and for projects with source files that
register new process-global Lean extensions while being elaborated. -/
def defaultMaxConcurrent : Nat := 1

private def sameImport (a b : Import) : Bool :=
  a.module == b.module && a.importAll == b.importAll &&
    a.isExported == b.isExported && a.isMeta == b.isMeta

private def pushImportOnce (imports : Array Import) (imp : Import) : Array Import :=
  if imports.any (sameImport · imp) then imports else imports.push imp

private def headerImportsOfFile (df : Discover.DiscoveredFile) : IO (Array Import) := do
  let source ← IO.FS.readFile df.absPath
  let inputCtx := Parser.mkInputContext source df.absPath.toString
  let (header, _, _) ← Parser.parseHeader inputCtx
  return Lean.Elab.headerToImports header

private def isDiscoveredModule (files : Array Discover.DiscoveredFile) (module : Name) : Bool :=
  files.any (fun df => df.module == module)

private def collectExternalHeaderImports (files : Array Discover.DiscoveredFile) : IO (Array Import) := do
  let mut imports : Array Import := #[]
  for df in files do
    for imp in (← headerImportsOfFile df) do
      unless isDiscoveredModule files imp.module do
        imports := pushImportOnce imports imp
  return imports

/-- Import external header dependencies once before parallel elaboration starts.
This forces dependency environment extensions and initializers to register
single-threaded, avoiding the known registry-growth race without eagerly loading
the package being extracted as `.olean`s. It cannot protect packages whose source
files themselves register new process-global extensions during elaboration, so
callers can keep `--jobs 1` for those packages. -/
unsafe def warmupImportRegistry (files : Array Discover.DiscoveredFile) : IO Unit := do
  let imports ← collectExternalHeaderImports files
  unless imports.isEmpty do
    IO.eprintln s!"corpus-extract: warming Lean import registry with {imports.size} external import(s)"
    Lean.enableInitializersExecution
    let _ ← Lean.importModules imports {} (trustLevel := 1024) (loadExts := true)
    IO.eprintln "corpus-extract: Lean import registry warmup complete"

/-- Elaborate every discovered file and apply `f` to each. Results are returned IN
INPUT ORDER; a file whose elaboration or collector throws is captured as
`Except.error` in that slot rather than aborting the batch (mirrors the old worker
driver's log-and-continue: one bad file never sinks the run). `f` always receives
`importLock` (the home for the mandatory per-file `enableInitializersExecution`
re-run inside `elaborateFile`).

`maxConcurrent ≤ 1` (the default — see `defaultMaxConcurrent`) takes the
**sequential** fast path: each file runs to completion on the calling thread, no
threads or semaphore. This is the correct-and-current mode.

`maxConcurrent > 1` first warms up imported modules single-threaded, then takes
the parallel path in bounded batches of at most `maxConcurrent` dedicated tasks.
The per-file header/import phase remains serialized behind `importLock`; the
command elaboration and collector body run in parallel. -/
unsafe def elaborateFiles {α} (files : Array Discover.DiscoveredFile)
    (f : ImportLock → Discover.DiscoveredFile → IO α)
    (maxConcurrent : Nat := defaultMaxConcurrent)
    : IO (Array (Except IO.Error α)) := do
  if maxConcurrent > 1 then
    warmupImportRegistry files
  let importLock : ImportLock ← Std.Mutex.new ()
  if maxConcurrent ≤ 1 then
    -- Sequential: run each file on the calling thread; `EIO.toBaseIO` captures a
    -- per-file error into the slot's `Except` so one bad file never aborts the
    -- batch. Order is input order.
    files.mapM fun df => (f importLock df).toBaseIO
  else
    -- Parallel path. Run bounded batches so `--jobs N` never creates more than N
    -- dedicated file tasks at a time.
    let mut out : Array (Except IO.Error α) := #[]
    let mut i := 0
    while i < files.size do
      let stop := Nat.min files.size (i + maxConcurrent)
      let batch := files.extract i stop
      let tasks ← batch.mapM fun df =>
        IO.asTask (prio := .dedicated) do
          f importLock df
      let results ← tasks.mapM fun t => IO.wait t
      out := out ++ results
      i := stop
    return out

end Corpus.Frontend
