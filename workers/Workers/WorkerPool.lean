/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Workers.Worker
import Workers.Cache
import Std.Sync.Mutex
import Std.Data.HashMap

/-!
A small LRU pool of file workers. Each consumer process owns one `WorkerPool` for the lifetime
of the process; tools call `acquire` to get (and possibly spawn) a worker for a given URI.

Eviction policy is straightforward LRU on `acquire` time: when the pool is full and a new URI is
requested, the least-recently-acquired URI is closed via `Worker.shutdown` before the new worker
is spawned. There is no explicit "close" tool yet — consumers that finish with a file simply let
it fall out of the LRU.
-/

namespace Workers

open Lean Lsp

/-- An entry in the pool. `lastUsed` is a monotonically increasing counter assigned on each
`acquire`; it is the LRU key. -/
structure Entry where
  worker   : Worker
  lastUsed : Nat

structure PoolState where
  /-- Active workers, keyed by URI. -/
  entries  : Std.HashMap DocumentUri Entry := ∅
  /-- Counter for `Entry.lastUsed`. -/
  tick     : Nat                            := 0

structure WorkerPool where
  state       : Std.Mutex PoolState
  workerPath  : System.FilePath
  forwardArgs : Array String
  maxSize     : Nat
  /-- Project root used to resolve relative `file_path` arguments. `none` means no resolution
  (relative paths are interpreted against the consumer process's CWD). -/
  projectRoot? : Option System.FilePath
  /-- Optional cache, used to compute `LEAN_PATH` additions when spawning workers. -/
  cache? : Option Cache
  /-- Spawn workers in their own session/process group (`setsid`). `true` (the default) matches
  the Watchdog: a long-lived server (mcp/verify) wants its workers isolated from terminal signals
  so a Ctrl-C at the user's editor doesn't reach them. A BATCH consumer (the corpus extractor)
  wants the opposite — workers should die with the parent — so it passes `false`: without `setsid`
  the workers stay in the parent's process group and a SIGTERM/SIGINT to the parent reaches them
  too, instead of leaving CPU-pinning orphans when the parent dies before `closeAll` runs. -/
  setsidWorkers : Bool

namespace WorkerPool

/-- Resolve the path of the `lean` binary to spawn workers from. Mirrors `Watchdog.findWorkerPath`. -/
private def findWorkerPath : IO System.FilePath := do
  let mut workerPath ← IO.appPath
  if let some path := (← IO.getEnv "LEAN_SYSROOT") then
    workerPath := System.FilePath.mk path / "bin" / "lean" |>.addExtension System.FilePath.exeExtension
  if let some path := (← IO.getEnv "LEAN_WORKER_PATH") then
    workerPath := System.FilePath.mk path
  return workerPath

/-- Validate that `path` looks like a Lean project root: it exists, is a directory, contains a
`lean-toolchain` file, and contains either `lakefile.toml` or `lakefile.lean`. -/
def validateProjectRoot (path : System.FilePath) : IO (Except String System.FilePath) := do
  let abs ← IO.FS.realPath path |>.catchExceptions fun _ => return path
  if ! (← abs.isDir) then
    return .error s!"Project path is not a directory: {abs}"
  if ! (← (abs / "lean-toolchain").pathExists) then
    return .error s!"Missing `lean-toolchain` in project root: {abs}"
  let hasToml ← (abs / "lakefile.toml").pathExists
  let hasLean ← (abs / "lakefile.lean").pathExists
  if ! (hasToml || hasLean) then
    return .error s!"Missing `lakefile.toml` or `lakefile.lean` in project root: {abs}"
  return .ok abs

/-- Build a fresh, empty pool. If `projectRoot?` is provided, it is `realpath`-ed and used to
resolve relative `file_path` arguments. If `cache?` is provided, its effective search path is
prepended to `LEAN_PATH` when spawning workers. -/
def new (maxSize : Nat := 4) (forwardArgs : Array String := #[])
    (projectRoot? : Option System.FilePath := none) (cache? : Option Cache := none)
    (setsidWorkers : Bool := true)
    : IO WorkerPool := do
  let state ← Std.Mutex.new ({} : PoolState)
  let workerPath ← findWorkerPath
  return { state, workerPath, forwardArgs, maxSize, projectRoot?, cache?, setsidWorkers }

/-- Resolve a `file_path` argument from a tool call against the pool's project root. Absolute
paths pass through unchanged. -/
def resolvePath (pool : WorkerPool) (path : System.FilePath) : System.FilePath :=
  if path.isAbsolute then
    path
  else
    match pool.projectRoot? with
    | some root => root / path
    | none      => path

/-- Look up a worker without bumping its LRU position. Used by tools that have already obtained a
URI from `acquire`. -/
def get? (pool : WorkerPool) (uri : DocumentUri) : IO (Option Worker) :=
  pool.state.atomically do
    let st ← get
    return st.entries.get? uri |>.map (·.worker)

/-- Build the env-var overrides we want to pass to each spawned worker. Currently this is just
`LEAN_PATH = <inherited>:<cache search paths>`; we leave `LEAN_PATH` untouched if there are no
extra paths to add, so the worker keeps its inherited search path. -/
private def buildExtraEnv (pool : WorkerPool) : IO (Array (String × Option String)) := do
  let some cache := pool.cache?
    | return #[]
  let extras ← cache.effectiveSearchPath
  if extras.isEmpty then
    return #[]
  let inherited := (← IO.getEnv "LEAN_PATH").getD ""
  let extraStr  := System.SearchPath.toString extras.toList
  let combined :=
    if inherited.isEmpty then extraStr
    else s!"{inherited}{System.SearchPath.separator}{extraStr}"
  return #[("LEAN_PATH", some combined)]

/-- Pick the LRU entry to evict, returning its URI (and removing it from the map). The caller
runs the actual `Worker.shutdown` outside the lock to avoid blocking other tools. -/
private def takeLruEntry
    : Std.AtomicT PoolState IO (Option (DocumentUri × Entry)) := do
  let st ← get
  let some (uri, _) := st.entries.toList.foldl
      (init := none) (fun best (uri, e) =>
        match best with
        | none           => some (uri, e.lastUsed)
        | some (_, used) => if e.lastUsed < used then some (uri, e.lastUsed) else best)
    | return none
  let some entry := st.entries.get? uri | return none
  set { st with entries := st.entries.erase uri }
  return some (uri, entry)

/-- Acquire a worker for `uri`, spawning one if necessary. The returned worker must already have
its `didOpen` sent (so `text` is the contents to use on first open). On a cache hit, `text` is
ignored — `Sync.ensureSynced` is responsible for issuing `didChange` to bring the worker up to
date.

On a cache hit we also check that the worker is still alive (the underlying process may have
exited e.g. because of an `importsChanged` signal). A dead worker is dropped from the pool and
respawned. -/
def acquire (pool : WorkerPool) (uri : DocumentUri) (text : String) : IO Worker := do
  -- Fast path: cache hit, just bump LRU.
  let hit? ← pool.state.atomically do
    let st ← get
    if let some entry := st.entries.get? uri then
      let tick' := st.tick + 1
      let entry' := { entry with lastUsed := tick' }
      set { st with entries := st.entries.insert uri entry', tick := tick' }
      return some entry.worker
    return none
  if let some w := hit? then
    if (← w.isDead) then
      -- Dead worker: drop it (it's already exited, no need to shutdown) and fall through to
      -- the spawn path below.
      pool.state.atomically <| modify fun st => { st with entries := st.entries.erase uri }
    else
      return w
  -- Miss: maybe evict, then spawn outside the lock. Spawning under the lock would serialize
  -- worker startup, which can take seconds while Lake builds dependencies.
  let evicted? ← pool.state.atomically do
    let st ← get
    if st.entries.size >= pool.maxSize then
      takeLruEntry
    else
      return none
  if let some (_, entry) := evicted? then
    let _ ← entry.worker.shutdown
  let extraEnv ← buildExtraEnv pool
  let w ← Worker.spawn uri text pool.workerPath pool.forwardArgs (extraEnv := extraEnv)
            (setsid := pool.setsidWorkers)
  pool.state.atomically do
    let st ← get
    let tick' := st.tick + 1
    let entry : Entry := { worker := w, lastUsed := tick' }
    set { st with entries := st.entries.insert uri entry, tick := tick' }
  return w

/-- Force-close the worker for `uri`, if any. -/
def close (pool : WorkerPool) (uri : DocumentUri) : IO Unit := do
  let entry? ← pool.state.atomically do
    let st ← get
    let entry? := st.entries.get? uri
    if entry?.isSome then set { st with entries := st.entries.erase uri }
    return entry?
  if let some entry := entry? then
    let _ ← entry.worker.shutdown

/-- Close all workers. Used on consumer shutdown. -/
def closeAll (pool : WorkerPool) : IO Unit := do
  let entries ← pool.state.atomically do
    let st ← get
    set ({} : PoolState)
    return st.entries
  for (_, entry) in entries do
    let _ ← entry.worker.shutdown

end WorkerPool

end Workers
