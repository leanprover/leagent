/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
`Corpus.ChildProcess` — bounded concurrency and child-process deadlines.

Two primitives every extraction path needs, each with exactly one implementation
here so their semantics are stated once:

  * `batchedMap` — run at most N tasks at a time over a list of work items,
    collecting per-item failures rather than aborting. Used to bound `--jobs`
    both for in-process file elaboration (`Corpus.Frontend`) and for isolated
    child processes (`Corpus.WorkerExtract`).
  * `ChildProcess.waitWithDeadline` — wait on a spawned child, killing it on
    expiry. The extractor bounds work it cannot cancel cooperatively by running it
    in a child and killing that child: a whole isolated file
    (`Corpus.WorkerExtract`) or one theorem's reverse-elaboration
    (`Corpus.CorpusManifest`).
-/

namespace Corpus

/-- Map `f` over `items` on dedicated tasks, at most `maxConcurrent` in flight, and
return the results IN INPUT ORDER. `f` receives each item's index alongside it.

Bounded batches rather than a semaphore: a batch is started, awaited, and only then
is the next started, so `--jobs N` never creates more than N tasks at a time. A
task's error is captured in its slot's `Except` (via `EIO.toBaseIO`) rather than
propagating, so one failure never aborts the batch. -/
def batchedMap {α β} (items : Array α) (maxConcurrent : Nat)
    (f : Nat → α → IO β) : IO (Array (Except IO.Error β)) := do
  let jobs := Nat.max 1 maxConcurrent
  let mut out : Array (Except IO.Error β) := #[]
  let mut i := 0
  while i < items.size do
    let stop := Nat.min items.size (i + jobs)
    let batch := items.extract i stop
    let mut tasks : Array (Task (Except IO.Error β)) := #[]
    for h : j in [0:batch.size] do
      tasks := tasks.push (← IO.asTask (prio := .dedicated) (f (i + j) batch[j]))
    out := out ++ (← tasks.mapM fun t => IO.wait t)
    i := stop
  return out

namespace ChildProcess

/-- Wait for `child`, killing it if `timeoutMs` elapses since `started`.

Returns the child's exit code, or `none` if it was killed on expiry. `timeoutMs = 0`
means no deadline (wait indefinitely). Polls rather than blocking so the deadline is
wall-clock: the bounded work may be a single uninterruptible `isDefEq`, which no
cooperative cancellation would preempt.

The `kill` is best-effort (a child that just exited raises, which we ignore) and is
always followed by `wait`, so the process is reaped rather than left a zombie. -/
partial def waitWithDeadline {cfg : IO.Process.StdioConfig}
    (child : IO.Process.Child cfg) (started timeoutMs : Nat) : IO (Option UInt32) := do
  match (← child.tryWait) with
  | some code => return some code
  | none =>
      if timeoutMs > 0 && (← IO.monoMsNow) - started ≥ timeoutMs then
        try child.kill catch _ => pure ()
        let _ ← child.wait
        return none
      IO.sleep (100 : UInt32)
      waitWithDeadline child started timeoutMs

end ChildProcess

end Corpus
