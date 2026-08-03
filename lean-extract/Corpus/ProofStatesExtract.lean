/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Corpus.Records
import Corpus.Discover
import Corpus.Frontend
import Corpus.FileDriver
import Corpus.ProofStates

/-!
Frontend-driven proof-state extraction: the per-file driver.

Runs the proof-state collector (`ProofStates.proofStatesCore`) over each elaborated
file, which walks that file's `InfoTree`s and returns one entry per tactic-proved
theorem. Each `ProofStateEntry` becomes a `ProofStateRecord` by attaching the
discovery relative path.

The driving, per-file error containment, and file/outcome counting are shared with
the other modes via `Corpus.FileDriver.driveFiles`. Here the per-file budget only
sheds the goal-rendering tail (`deadline_skipped`), never a file's records.
-/

namespace Corpus

open Lean

/-- The two counters specific to proof-state extraction: term-proved theorems (which
have no tactics and so are counted rather than emitted) and total steps across every
emitted record. Everything else this mode reports is in `FileDriver.FileStats`. -/
structure ProofStateExtras where
  theoremsTermProved : Nat := 0
  totalSteps         : Nat := 0
  deriving Inhabited

/-- The outcome labels the proof-state run summary reports individually; anything
else is counted as an error. -/
def proofStateOutcomeLabels : List String :=
  [Outcome.ok, Outcome.skippedLarge, Outcome.deadlineSkipped]

/-- Map one collector entry to a wire record. `relFile` is the project-relative
source path from discovery — the one thing the collector cannot know. -/
def proofStateEntryToRecord (e : ProofStates.ProofStateEntry) (relFile : String)
    : ProofStateRecord :=
  { name           := e.name
    module         := e.module
    file           := some relFile
    startLine      := e.startLine
    startCol       := e.startCol
    endLine        := e.endLine
    endCol         := e.endCol
    declKind       := e.declKind
    proofStartByte := e.proofStartByte
    proofEndByte   := e.proofEndByte
    proofSource    := e.proofSource
    parentDecl     := e.parentDecl
    goals          := e.goals
    initialGoals   := e.initialGoals
    steps          := e.steps
    stepCount      := e.stepCount
    maxDepth       := e.maxDepth
    tacticKinds    := e.tacticKinds
    hasSorry       := e.hasSorry
    outcome        := e.outcome
    isPrivate      := e.isPrivate }

/-- Per-file proof-state timeout (ms). Goal rendering is `ppExpr`-bound rather
than search-bound, so this is generous: it exists to stop one pathological file
from stalling a run, not to shape normal output. -/
def proofStateFileTimeoutMs : Nat := 300000

/-- Drive every discovered file through the frontend and collect
`ProofStateRecord`s. Per-file errors are logged to stderr and counted, never
fatal — one bad file must not sink the run (the same log-and-continue contract
the other drivers keep).

`unsafe` because in-process elaboration runs imported modules' interpreted
`initialize` code (see `Frontend.elaborateFile`). -/
unsafe def extractProofStatesViaFrontend (files : Array Discover.DiscoveredFile)
    (includePrivate : Bool) (jobs : Nat := Frontend.defaultMaxConcurrent)
    : IO (Array ProofStateRecord × FileDriver.FileStats × ProofStateExtras) := do
  let deadlineMs := FileDriver.deadlineFor proofStateFileTimeoutMs
  let (results, stats) ← FileDriver.driveFiles files
    (collect := fun r => do
      let (entries, skippedTerm) ← ProofStates.proofStatesCore r includePrivate deadlineMs
      pure (skippedTerm, entries))
    (outcomeOf := (some ·.outcome))
    (jobs := jobs)
  let recs := results.flatMap fun fr =>
    fr.entries.map fun e => proofStateEntryToRecord e fr.file.relPath
  -- The two counters that are this mode's own: term-proved theorems (per file, and
  -- deliberately not emitted as records) and total steps (per entry).
  let extras : ProofStateExtras := {
    theoremsTermProved := results.foldl (init := 0) fun acc fr => acc + fr.extra
    totalSteps := results.foldl (init := 0) fun acc fr =>
      fr.entries.foldl (init := acc) fun a e => a + e.stepCount }
  return (recs, stats, extras)

end Corpus
