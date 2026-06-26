/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Std.Sync.Mutex
import Init.System.IO
import Init.System.FilePath

/-!
A simple search-path / artifact cache, used by `WorkerPool` to populate `LEAN_PATH` for spawned
workers without rebuilding from source.

Two ways to populate the list:

- **Search path** (`setSearchPath`): the caller points at directories that already exist
  on the filesystem (e.g. a pre-populated `~/.cache/lake/...` directory). Useful when
  the harness has already done a `lake build` or `lake cache get`.
- **Per-process upload cache** (`putArtifact`): the caller uploads `.olean` (or
  `.ilean`) bytes; the cache writes them under a temp directory whose layout matches Lean's
  module-name → file-path mapping. The temp directory is automatically on the search path.

Changing either source requires evicting all live workers — workers were spawned with a frozen
`LEAN_PATH` and won't pick up the new directory otherwise. The eviction policy belongs to the
consumer; this module only manages the path list.
-/

namespace Workers

/-- Mutable state held by `Cache`. -/
structure CacheState where
  /-- Directories the consumer has explicitly added via `setSearchPath`. -/
  searchPath : Array System.FilePath := #[]

/-- A simple cache. One per consumer process. -/
structure Cache where
  state : Std.Mutex CacheState
  /-- Directory under which `putArtifact` materializes uploaded oleans. Always on
  the effective search path. Created lazily on first upload. -/
  uploadDir : System.FilePath

namespace Cache

/-- Per-process upload directory, scoped by PID. Subdirectory name `lean-server-cache-{pid}` is
just a label for human readability when inspecting `${TMPDIR}`. -/
private def defaultUploadDir : IO System.FilePath := do
  let base : System.FilePath :=
    match (← IO.getEnv "TMPDIR") with
    | some t => System.FilePath.mk t
    | none   => System.FilePath.mk "/tmp"
  let pid ← IO.Process.getPID
  return base / s!"lean-server-cache-{pid}" / "cache"

def new : IO Cache := do
  let state ← Std.Mutex.new ({} : CacheState)
  let uploadDir ← defaultUploadDir
  return { state, uploadDir }

/-- Replace the consumer-supplied search path with a new list. Caller is responsible for
evicting workers that were spawned with the old `LEAN_PATH`. -/
def setSearchPath (c : Cache) (paths : Array System.FilePath) : IO Unit :=
  c.state.atomically <| modify fun st => { st with searchPath := paths }

/-- Read the consumer-supplied search path. -/
def getSearchPath (c : Cache) : IO (Array System.FilePath) := do
  let st ← c.state.atomically get
  return st.searchPath

/-- The full list of additional directories to expose to workers via `LEAN_PATH`. This is the
consumer's `searchPath` plus the upload directory (always last so user-supplied paths take
precedence). -/
def effectiveSearchPath (c : Cache) : IO (Array System.FilePath) := do
  let user ← c.getSearchPath
  return user.push c.uploadDir

/-- Convert a Lean module name like `Mathlib.Data.Nat.Basic` to the relative `.olean` path
`Mathlib/Data/Nat/Basic.olean`. -/
private def moduleToOleanPath (name : String) (ext : String) : System.FilePath :=
  let parts := name.splitOn "."
  let path := System.FilePath.mk (String.intercalate "/" parts)
  path.addExtension ext

/-- Materialize uploaded artifact bytes under `uploadDir`. `name` is the Lean module name
(e.g. `Mathlib.Data.Nat.Basic`); `ext` is one of `"olean"`, `"ilean"`, `"olean.hash"`, etc.

Returns the absolute path of the written file. -/
def putArtifact (c : Cache) (name : String) (ext : String) (bytes : ByteArray) : IO System.FilePath := do
  let rel := moduleToOleanPath name ext
  let path := c.uploadDir / rel
  if let some parent := path.parent then
    IO.FS.createDirAll parent
  IO.FS.writeBinFile path bytes
  return path

/-- Best-effort cleanup of the upload directory. Called from the consumer's shutdown path. -/
def cleanup (c : Cache) : IO Unit := do
  try IO.FS.removeDirAll c.uploadDir catch _ => pure ()

end Cache

end Workers
