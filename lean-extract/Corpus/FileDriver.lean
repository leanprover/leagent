/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Corpus.Discover
import Corpus.Frontend
import Corpus.Options

/-!
`Corpus.FileDriver` — the shape every per-file extraction mode shares.

Each mode (corpus, grind, in-proof grind, proof states) elaborates the same set of
discovered files, runs its own `CoreM` collector over each one, and folds the
per-file results into records plus a run summary. Only the collector and the
entry→record mapping differ; the driving, the per-file error containment, and the
file/outcome counting are identical.

`driveFiles` is that common part:

  * elaborate each file (`Frontend.elaborateFiles`, so per-file errors land in the
    result slot rather than aborting the batch),
  * run `collect` on each elaborated file,
  * tally `filesOk` / `filesEmpty` / `filesError` and log each failure once,
  * tally each entry's `outcome` label into a map.

What it deliberately does NOT do is accumulate a mode's extra per-file value (the
grind modes' `available` hint set, proof states' term-proved count) or its extra
per-entry value (proof states' step count). Those stay in the caller, which is
where they are readable — the combinator owns only what is genuinely the same.

The per-file deadline convention also lives here (`deadlineFor`): every mode sets
its collector's internal budget to 80% of its own per-file bound, so the expensive
tail sheds cooperatively instead of the file dying outright.
-/

namespace Corpus.FileDriver

open Lean

/-- File-level counters plus an outcome tally, shared by every mode's run summary.
`outcomes` maps an entry's `outcome` label to how many entries carried it, so a new
label needs no new field. -/
structure FileStats where
  filesTotal : Nat := 0
  filesOk    : Nat := 0
  filesEmpty : Nat := 0
  filesError : Nat := 0
  outcomes   : Std.HashMap String Nat := {}
  deriving Inhabited

/-- Count of entries whose `outcome` was `label`. -/
def FileStats.outcome (s : FileStats) (label : String) : Nat :=
  s.outcomes.getD label 0

/-- Count of entries whose `outcome` was NOT any of `labels` — the "everything
else" bucket each mode reports as its error count. -/
def FileStats.outcomesOther (s : FileStats) (labels : List String) : Nat :=
  s.outcomes.fold (init := 0) fun acc label n =>
    if labels.contains label then acc else acc + n

/-- A collector's internal wall-clock budget: 80% of the mode's per-file bound,
leaving headroom so the tail sheds (`deadline_skipped`) rather than the file dying. -/
def deadlineFor (fileTimeoutMs : Nat) : Nat := fileTimeoutMs * 4 / 5

/-- One file's successful result: the file it came from and the entries collected. -/
structure FileResult (Extra Entry : Type) where
  file    : Discover.DiscoveredFile
  extra   : Extra
  entries : Array Entry

/-- Elaborate every discovered file, run `collect` on each, and return the
successful per-file results alongside the shared counters.

`outcomeOf` names each entry's outcome for the tally.

`progressLabel`, when given, prints one `starting`/`finished`/`failed` line per file
under that label; `none` (the default) is silent. The vocabulary is fixed at those
three verbs deliberately — a caller needing different ones (the isolated driver also
reports `reused shard` / `timed out` / `recovered`) does its own logging rather than
widening this.

A file whose elaboration reports Lean errors is treated as a failure, matching the
corpus contract that a broken file must not silently yield zero records.

Per-file failures are logged to stderr and counted in `filesError`; they never abort
the run, so one bad file cannot sink an extraction.

`unsafe` because in-process elaboration runs imported modules' interpreted
`initialize` code (see `Frontend.elaborateFile`). -/
unsafe def driveFiles {Extra Entry : Type}
    (files : Array Discover.DiscoveredFile)
    (collect : Frontend.ElabResult → IO (Extra × Array Entry))
    (outcomeOf : Entry → Option String := fun _ => none)
    (jobs : Nat := Frontend.defaultMaxConcurrent)
    (progressLabel : Option String := none)
    (rejectFileErrors : Bool := false)
    : IO (Array (FileResult Extra Entry) × FileStats) := do
  Frontend.initFrontend
  let startedRef ← IO.mkRef 0
  let finishedRef ← IO.mkRef 0
  -- Progress lines are numbered by COMPLETION order: under `--jobs N` the counter
  -- says how many files have reached this point, not which file this is.
  let note (ref : IO.Ref Nat) (what : String) : IO Unit := do
    if let some label := progressLabel then
      let i ← ref.modifyGet fun n => (n + 1, n + 1)
      IO.eprintln s!"corpus-extract: {label} {i}/{files.size} {what}"
  let results ← Frontend.elaborateFiles files (fun importLock df => do
    note startedRef s!"starting {df.relPath}"
    try
      let r ← Frontend.elaborateFile importLock df
      if rejectFileErrors && r.hasErrors then
        throw <| IO.userError s!"Lean reported errors while elaborating {df.relPath}"
      let (extra, entries) ← collect r
      note finishedRef s!"finished {df.relPath} ({entries.size} record(s))"
      pure ({ file := df, extra, entries } : FileResult Extra Entry)
    catch e =>
      note finishedRef s!"failed {df.relPath}: {e.toString}"
      throw e)
    (maxConcurrent := jobs)
  let mut out   : Array (FileResult Extra Entry) := #[]
  let mut stats : FileStats := { filesTotal := files.size }
  for res in results do
    match res with
    | .ok fr =>
      if fr.entries.isEmpty then
        stats := { stats with filesEmpty := stats.filesEmpty + 1 }
      else
        stats := { stats with filesOk := stats.filesOk + 1 }
      for e in fr.entries do
        if let some label := outcomeOf e then
          stats := { stats with
            outcomes := stats.outcomes.insert label (stats.outcomes.getD label 0 + 1) }
      out := out.push fr
    | .error msg =>
      stats := { stats with filesError := stats.filesError + 1 }
      IO.eprintln s!"corpus-extract: {msg}"
  return (out, stats)

end Corpus.FileDriver
