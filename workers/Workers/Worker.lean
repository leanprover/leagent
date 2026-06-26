/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean.Data.Lsp.Communication
import Lean.Data.Lsp.TextSync
import Lean.Data.Lsp.Extra
import Lean.Data.Lsp.InitShutdown
import Lean.Data.Lsp.Capabilities
import Lean.Data.Lsp.Diagnostics
import Std.Sync.Channel
import Std.Sync.Mutex
import Init.System.IO

/-!
A `Worker` is a `lean --worker` subprocess driving elaboration for a single Lean file.

This module is intentionally a thin shim around `Process.spawn`: it spawns the worker, sends
`initialize` and the initial `didOpen`, and runs an async task that reads worker stdout and
demultiplexes messages onto:

- `diagnosticsRef` — most recent `textDocument/publishDiagnostics` per document version
- `progressRef`   — most recent `$/lean/fileProgress` notification (used to detect idle)
- `pendingRef`    — promises filled by request responses (`textDocument/hover` etc.)

Other notifications (`$/lean/ileanInfoFinal`, `$/lean/importClosure`, etc.) are dropped for now.
The Watchdog handles much more (request queues, restart-on-crash, replay state); none of that is
needed when our "client" is a tool call: each tool either gets its response or fails.

This module is the substrate driver: nothing here depends on MCP, lean-mcp, lean-verify, or any
other particular consumer. The downstream packages each consume this library directly.
-/

namespace Workers

open Lean Lsp JsonRpc IO

/-- Stdio configuration matching the Watchdog's `workerCfg`. -/
@[reducible] def workerStdioCfg : IO.Process.StdioConfig where
  stdin  := IO.Process.Stdio.piped
  stdout := IO.Process.Stdio.piped
  -- Pass the worker's stderr through unchanged. Lake build progress prints there.
  stderr := IO.Process.Stdio.inherit

/-- One-shot response slot. The reader task resolves the promise when the response arrives. -/
abbrev ResponseSlot := IO.Promise JsonRpc.Message

structure Worker where
  /-- File URI this worker owns. -/
  uri        : DocumentUri
  /-- Underlying `lean --worker` subprocess. -/
  proc       : IO.Process.Child workerStdioCfg
  /-- Monotonically increasing document version used in `didChange` notifications. -/
  versionRef : IO.Ref Nat
  /-- Cached most recent file contents we sent to the worker. Used for diff-based `didChange`. -/
  contentRef : IO.Ref String
  /-- Most recent `$/lean/fileProgress` notification, exposed for "wait until idle" tooling. -/
  progressRef : IO.Ref (Option LeanFileProgressParams)
  /-- Diagnostics for the current document version, accumulated as the worker emits them. -/
  diagnosticsRef : IO.Ref (Std.HashMap Int PublishDiagnosticsParams)
  /-- Pending request → response slot. The reader task fills the slot when a response arrives. -/
  pendingRef : Std.Mutex (Std.HashMap RequestID ResponseSlot)
  /-- Reader task; finishes when the worker stdout closes. -/
  readerTask : Task (Except IO.Error Unit)

namespace Worker

/-- Stdin stream of the worker subprocess. -/
private def stdin (w : Worker) : IO.FS.Stream :=
  IO.FS.Stream.ofHandle w.proc.stdin

/-- Stdout stream of the worker subprocess. -/
private def stdout (w : Worker) : IO.FS.Stream :=
  IO.FS.Stream.ofHandle w.proc.stdout

/-- Write any LSP message to the worker. -/
def writeMessage (w : Worker) (m : JsonRpc.Message) : IO Unit :=
  w.stdin.writeLspMessage m

/-- Send a notification with no parameters. -/
private def sendBareNotification (w : Worker) (method : String) : IO Unit :=
  w.writeMessage (JsonRpc.Message.notification method none)

/-- Send a typed LSP request. The reader task resolves the returned promise when the response
arrives. If the worker exits before responding, the promise is dropped. -/
def sendRequest [ToJson α] (w : Worker) (id : RequestID) (method : String) (params : α)
    : IO ResponseSlot := do
  let slot ← IO.Promise.new
  w.pendingRef.atomically <| modify (·.insert id slot)
  w.stdin.writeLspRequest ⟨id, method, params⟩
  return slot

/-- Block until `slot` is filled (response arrived) or the worker's reader task ends (because
the worker closed its stdout, so no more responses will come).

`Promise.result?.get` only returns `none` when the promise is *dropped* unresolved, but here both
the caller and `pendingRef` keep it alive — so a naive `slot.result?.get` would block forever
if the worker died mid-request. We instead poll: `readerLoop`'s `finally` clause is the common
case (it drains pending slots into a synthetic error), and the `IO.hasFinished w.readerTask`
check is a backstop for the rare race where a request is registered *after* that drain.

`timeoutMs` bounds the wait: `0` (the default) means wait forever, preserving the original
behavior for the interactive consumers (hover/definition/etc., where the worker either responds
or its stdout closes). A nonzero deadline matters when a request can make the worker compute
*unboundedly without exiting* — e.g. `$/lean/corpusManifest` with reverse-elaboration on a
pathological proof. Such a worker is alive (so the `readerTask` backstop never fires) yet will
never respond, so only a deadline unwedges the client. On timeout we throw; the caller is
expected to discard the worker (it is busy and cannot be reused). Mirrors the deadline structure
of `waitForDiagnostics`. -/
partial def awaitResponse (w : Worker) (slot : ResponseSlot) (timeoutMs : Nat := 0)
    : IO JsonRpc.Message := do
  -- Fast path: if the reader already resolved the slot, return immediately.
  if (← IO.hasFinished slot.result?) then
    match slot.result?.get with
    | some m => return m
    | none   => throw <| .userError "Workers: worker promise dropped without resolution"
  let stepMs : Nat := 20
  let mut waited : Nat := 0
  while true do
    IO.sleep stepMs.toUInt32
    if (← IO.hasFinished slot.result?) then
      match slot.result?.get with
      | some m => return m
      | none   => break
    if (← IO.hasFinished w.readerTask) then
      -- Reader is done. The drain in `readerLoop`'s `finally` should have resolved our slot;
      -- check once more in case it just landed. Otherwise (insertion-after-drain race) bail.
      if (← IO.hasFinished slot.result?) then
        match slot.result?.get with
        | some m => return m
        | none   => break
      throw <| .userError "Workers: worker exited before responding"
    -- Deadline check (only when `timeoutMs > 0`). The worker may be alive but spinning on a
    -- request it will never answer, which neither branch above catches.
    waited := waited + stepMs
    if timeoutMs != 0 && waited >= timeoutMs then
      throw <| .userError s!"Workers: timed out after {timeoutMs}ms waiting for worker response"
  throw <| .userError "Workers: worker promise dropped without resolution"

/-- Send the `initialize` request to the worker. Note: the worker does *not* send a response
(see `Lean.Server.Watchdog.lean:54`); the watchdog forwards `initialize` for protocol shape but
the worker just consumes it. So we don't wait for a response. -/
def sendInitialize (w : Worker) (initParams : InitializeParams) : IO Unit :=
  w.stdin.writeLspRequest ⟨"init", "initialize", initParams⟩

/-- Send a `textDocument/didOpen` for the URI this worker owns, with the given contents. -/
def didOpen (w : Worker) (text : String) (mode : DependencyBuildMode := .always) : IO Unit := do
  let version ← w.versionRef.get
  let params : LeanDidOpenTextDocumentParams := {
    textDocument := { uri := w.uri, languageId := "lean", version, text }
    dependencyBuildMode? := some mode
  }
  w.stdin.writeLspNotification ⟨"textDocument/didOpen", params⟩
  w.contentRef.set text

/-- Send a `textDocument/didChange`. The caller is responsible for updating `contentRef` to match
the resulting document state (so future diffs use the right basis). `changes` is a sequence of
LSP `TextDocumentContentChangeEvent`s. -/
def didChange (w : Worker) (changes : Array TextDocumentContentChangeEvent) (newText : String)
    : IO Unit := do
  let version ← w.versionRef.modifyGet fun n => (n + 1, n + 1)
  let params : DidChangeTextDocumentParams := {
    textDocument := { uri := w.uri, version? := some version }
    contentChanges := changes
  }
  -- Drop diagnostics for older versions; the worker is about to re-elaborate.
  w.diagnosticsRef.modify (·.erase ((version : Int) - 1))
  w.stdin.writeLspNotification ⟨"textDocument/didChange", params⟩
  w.contentRef.set newText

/-- Resolve every still-pending response slot with a synthetic `responseError`. Called from
`readerLoop`'s `finally` so anyone blocked in `awaitResponse` unblocks when the worker closes
its stdout (instead of hanging forever waiting on a promise nothing will ever resolve). -/
private def drainPendingOnExit (w : Worker) : IO Unit := do
  let pending ← w.pendingRef.atomically do
    let map ← get
    set (∅ : Std.HashMap RequestID ResponseSlot)
    return map
  for (id, slot) in pending do
    slot.resolve <| JsonRpc.Message.responseError id .internalError
      "Workers: worker exited before responding" none

/-- Read messages from worker stdout in a loop, dispatching each to the appropriate channel /
ref. Returns when stdout closes; resolves any outstanding pending slots on the way out so
`awaitResponse` callers don't hang. -/
private partial def readerLoop (w : Worker) : IO Unit := do
  let rec loop : IO Unit := do
    let msg ← w.stdout.readLspMessage
    match msg with
    | JsonRpc.Message.notification "textDocument/publishDiagnostics" (some p) =>
      if let .ok params := (fromJson? (toJson p) : Except _ PublishDiagnosticsParams) then
        let v := params.version?.getD 0
        w.diagnosticsRef.modify (·.insert v params)
    | JsonRpc.Message.notification "$/lean/fileProgress" (some p) =>
      if let .ok params := (fromJson? (toJson p) : Except _ LeanFileProgressParams) then
        w.progressRef.set (some params)
    | JsonRpc.Message.notification _ _ =>
      -- Drop other notifications (ileanInfo*, importClosure, ...) for now.
      pure ()
    | JsonRpc.Message.response id _ | JsonRpc.Message.responseError id _ _ _ =>
      let slot? ← w.pendingRef.atomically do
        let map ← get
        let slot? := map.get? id
        if slot?.isSome then set (map.erase id)
        return slot?
      if let some slot := slot? then
        slot.resolve msg
    | JsonRpc.Message.request _ _ _ =>
      pure ()
    loop
  try
    loop
  finally
    drainPendingOnExit w

/-- Spawn a `lean --worker` for `uri`, send the initial handshake, and start the reader task.

`workerPath` is the `lean` binary to exec; defaults to the currently running binary. `forwardArgs`
is appended after `--worker` so callers can forward `-D…`, `--load-dynlib=…`, etc. `extraEnv`
is appended to the spawn's env (used by the cache layer to set `LEAN_PATH`).

`setsid` (default `true`, matching the Watchdog) starts the worker in its own session/process
group, isolating it from terminal signals — right for a long-lived server, but it also means the
worker outlives a parent that dies without running `shutdown`. A batch consumer passes `false` so
its workers share the parent's process group and die with it (no CPU-pinning orphans). -/
def spawn (uri : DocumentUri) (text : String) (workerPath : System.FilePath)
    (forwardArgs : Array String := #[])
    (initParams : InitializeParams := { capabilities := ({} : ClientCapabilities) })
    (mode : DependencyBuildMode := .always)
    (extraEnv : Array (String × Option String) := #[])
    (setsid : Bool := true) : IO Worker := do
  let proc ← IO.Process.spawn {
    toStdioConfig := workerStdioCfg
    cmd  := workerPath.toString
    args := #["--worker"] ++ forwardArgs ++ #[uri]
    env  := extraEnv
    setsid := setsid
  }
  let versionRef     ← IO.mkRef 1
  let contentRef     ← IO.mkRef ""
  let progressRef    ← IO.mkRef (none : Option LeanFileProgressParams)
  let diagnosticsRef ← IO.mkRef (∅ : Std.HashMap Int PublishDiagnosticsParams)
  let pendingRef     ← Std.Mutex.new (∅ : Std.HashMap RequestID ResponseSlot)
  -- The reader task captures the worker handle; we tie the knot by giving the field a
  -- dummy task initially, then overwriting it with the real reader task before doing the
  -- handshake. The reader only ever touches `proc.stdout` and the refs, so this is safe.
  let dummy : Task (Except IO.Error Unit) := Task.pure (.ok ())
  let w : Worker := {
    uri, proc, versionRef, contentRef, progressRef, diagnosticsRef, pendingRef
    readerTask := dummy
  }
  let task ← (readerLoop w).asTask (prio := .dedicated)
  let w := { w with readerTask := task }
  w.sendInitialize initParams
  w.didOpen text mode
  return w

/-- Send `exit` and wait for the worker to terminate. -/
def shutdown (w : Worker) : IO UInt32 := do
  try w.sendBareNotification "exit" catch _ => pure ()
  try w.proc.kill catch _ => pure ()
  w.proc.wait

/-- Snapshot diagnostics for the current document version (or `none` if not yet emitted). -/
def currentDiagnostics (w : Worker) : IO (Option PublishDiagnosticsParams) := do
  let v ← w.versionRef.get
  let map ← w.diagnosticsRef.get
  return map.get? (v : Int)

/-- Result of `waitForDiagnostics`. Distinguishing these lets callers surface accurate errors
to the agent instead of returning empty/stale state. -/
inductive WaitResult where
  /-- Worker resolved the request: diagnostics for the current version are ready. -/
  | done
  /-- Timed out before the worker responded. -/
  | timeout
  /-- The worker exited (or its reader task ended) before responding. -/
  | workerExited
  deriving Repr, BEq

/-- Send `textDocument/waitForDiagnostics` and block until the worker resolves it. The worker
only sends the response once it has emitted all diagnostics for the requested document version,
which is exactly the synchronization point we want before reading `currentDiagnostics`. -/
partial def waitForDiagnostics (w : Worker) (timeoutMs : Nat := 60000) : IO WaitResult := do
  let v ← w.versionRef.get
  let id : RequestID := s!"waitForDiagnostics/{v}"
  let slot ← w.sendRequest id "textDocument/waitForDiagnostics"
    ({ uri := w.uri, version := v } : WaitForDiagnosticsParams)
  -- Poll the promise against a deadline. We also bail if the reader task finished, which
  -- means the worker closed stdout and is never going to respond.
  let stepMs : Nat := 20
  let mut waited : Nat := 0
  let mut result : WaitResult := .timeout
  while waited < timeoutMs do
    if (← IO.hasFinished slot.result?) then
      result := .done
      break
    if (← IO.hasFinished w.readerTask) then
      result := .workerExited
      break
    IO.sleep stepMs.toUInt32
    waited := waited + stepMs
  w.pendingRef.atomically <| modify (·.erase id)
  return result

/-- Quick liveness check: returns `true` if the worker process has exited. This lets the pool
discard dead workers so the next `acquire` spawns a fresh one. -/
def isDead (w : Worker) : IO Bool := do
  match (← w.proc.tryWait) with
  | some _ => return true
  | none   => return false

end Worker

end Workers
