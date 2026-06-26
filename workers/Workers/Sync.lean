/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Workers.WorkerPool
import Workers.Document
import Init.Data.String.Extra

/-!
Bridges path-based requests against the worker pool: read a file from disk, spawn or sync the
matching worker, and wait for elaboration to settle. Each call goes through `ensureSynced path`:

1. Read the file from disk and normalize CRLF → LF.
2. If no worker exists for this URI, spawn one (`acquire`) and `didOpen` with the contents.
3. Otherwise, diff the cached contents against the new contents and send a single `didChange`
   (range or full).
4. Wait until elaboration is idle, so subsequent LSP requests see fresh state.

The cached contents live on the `Worker` (in `contentRef`), not on a side map — there is exactly
one source of truth for "what the worker thinks the document is right now."

This module is consumer-agnostic: the only hook is `onSync?`, an optional callback that
fires once per successful sync. Auditing layers (e.g. lean-mcp's session-touched-set) wire
themselves in via this callback.
-/

namespace Workers

open Lean Lsp

/-- Read `path` and normalize line endings. -/
private def readNormalized (path : System.FilePath) : IO String := do
  let raw ← IO.FS.readFile path
  return raw.crlfToLf

/-- Result of `ensureSynced`. -/
inductive SyncResult where
  | ok      (w : Worker)
  /-- The file does not exist on disk. -/
  | missing (path : System.FilePath)
  /-- The worker for this URI exited before reporting diagnostics. -/
  | workerExited (uri : DocumentUri)
  /-- The worker did not finish elaborating within the timeout. -/
  | timeout (uri : DocumentUri)

/-- Bring the worker for `uri` (spawning if needed) up to the current contents of `path`, then
wait for elaboration to settle.

`path` is resolved against `pool.projectRoot?` if it is relative; the result is then
canonicalized via `realPath` so symlinks and `..` segments don't fragment the worker pool.

`onSync?` is a per-call hook fired with the resolved URI as soon as the worker is acquired
(before `didChange` and `waitForDiagnostics`). Consumers use this to build session-scoped
audit trails or change-tracking sets without having the substrate know what an "audit" is. -/
def ensureSynced (pool : WorkerPool) (path : System.FilePath) (timeoutMs : Nat := 60000)
    (onSync? : Option (DocumentUri → IO Unit) := none) : IO SyncResult := do
  let resolved := pool.resolvePath path
  if ! (← resolved.pathExists) then
    return .missing resolved
  let abs ← IO.FS.realPath resolved
  let uri := System.Uri.pathToUri abs
  let contents ← readNormalized abs
  let w ← pool.acquire uri contents
  if let some onSync := onSync? then
    onSync uri
  -- Cache hit: send `didChange` if the contents differ.
  let cached ← w.contentRef.get
  if cached != "" && cached != contents then
    if let some change := diffToChange cached contents then
      w.didChange #[change] contents
  match (← w.waitForDiagnostics timeoutMs) with
  | .done         => return .ok w
  | .timeout      => return .timeout uri
  | .workerExited =>
    -- Worker died: drop it from the pool so the next call respawns.
    pool.close uri
    return .workerExited uri

end Workers
