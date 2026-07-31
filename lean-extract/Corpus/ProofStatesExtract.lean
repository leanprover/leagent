/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Corpus.Records
import Corpus.Discover
import Corpus.Frontend
import Corpus.ProofStates

/-!
Frontend-driven proof-state extraction: the per-file driver.

Parallel to `Corpus.GrindInProofExtract`, but runs the proof-state collector
(`ProofStates.proofStatesCore`) instead of a grind one. For each source file it
elaborates the file in-process (`Frontend.elaborateFile`), then asks the collector
to walk that file's `InfoTree`s and return one entry per tactic-proved theorem.
Each `ProofStateEntry` becomes a `ProofStateRecord` by attaching the discovery
relative path.

See `Corpus.GrindExtract` for the shared per-file bounding rationale; here the
per-file budget only sheds the goal-rendering tail (`deadline_skipped`), never a
file's records.
-/

namespace Corpus

open Lean

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
unsafe def extractProofStatesViaFrontend (projectRoot : System.FilePath)
    (files : Array Discover.DiscoveredFile) (includePrivate : Bool)
    (jobs : Nat := Frontend.defaultMaxConcurrent)
    : IO (Array ProofStateRecord × ProofStateRunStats) := do
  let _ := projectRoot  -- discovery already resolved paths; kept for signature parity
  Frontend.initFrontend
  -- Leave headroom below the per-file bound so the tail sheds rather than dies.
  let deadlineMs := proofStateFileTimeoutMs * 4 / 5
  let results ← Frontend.elaborateFiles files (fun importLock df => do
    let r ← Frontend.elaborateFile importLock df
    let (entries, skippedTerm) ← ProofStates.proofStatesCore r includePrivate deadlineMs
    pure (df, entries, skippedTerm)) (maxConcurrent := jobs)
  let mut recs  : Array ProofStateRecord := #[]
  let mut stats : ProofStateRunStats := { filesTotal := files.size }
  for res in results do
    match res with
    | .ok (df, entries, skippedTerm) =>
      if entries.isEmpty then
        stats := { stats with filesEmpty := stats.filesEmpty + 1 }
      else
        stats := { stats with filesOk := stats.filesOk + 1 }
      stats := { stats with
        theoremsSkippedTerm := stats.theoremsSkippedTerm + skippedTerm }
      for e in entries do
        recs := recs.push (proofStateEntryToRecord e df.relPath)
        stats := { stats with totalSteps := stats.totalSteps + e.stepCount }
        stats := match e.outcome with
          | "ok"               => { stats with theoremsOk := stats.theoremsOk + 1 }
          | "skipped_large"    => { stats with
              theoremsSkippedLarge := stats.theoremsSkippedLarge + 1 }
          | "deadline_skipped" => { stats with
              theoremsDeadline := stats.theoremsDeadline + 1 }
          | _                  => { stats with
              theoremsError := stats.theoremsError + 1 }
    | .error msg =>
      stats := { stats with filesError := stats.filesError + 1 }
      IO.eprintln s!"corpus-extract: {msg}"
  return (recs, stats)

end Corpus
