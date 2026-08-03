import Lean
import Corpus.Records
import Corpus.Discover
import Corpus.Frontend
import Corpus.FileDriver
import Corpus.GrindExtract
import Corpus.GrindInProof

/-!
Frontend-driven in-proof grind extraction: the observation-mode collector.

Where `Corpus.GrindExtract` re-proves whole statements, this walks each file's
`InfoTree`s for every `grind` CALL SITE inside a proof, re-runs instrumented grind on
each restored subgoal (with the author's hints), and reports the triple plus
artifacts. Each `GrindInProofEntry` becomes a `GrindInProofRecord` (adding the `file`
path from discovery); the per-file `available` hint sets are merged into one.

See `Corpus.GrindExtract` for the shared cooperative-bounding rationale (per-goal
`grindHeartbeats` + the per-file deadline) and the shared driving via
`Corpus.FileDriver.driveFiles`.
-/

namespace Corpus

open Lean

/-- Map one `GrindInProofEntry` (a grind call site) to a `GrindInProofRecord`.
`relFile` is the project-relative source path from discovery. -/
def grindInProofEntryToRecord (e : GrindInProofEntry) (relFile : String)
    : GrindInProofRecord :=
  { enclosingTheorem := e.enclosingTheorem
    module           := e.module
    file             := some relFile
    startLine        := e.startLine
    startCol         := e.startCol
    goalType         := e.goalType
    authorHints      := e.authorHints
    authorOnly       := e.authorOnly
    outcome          := e.outcome
    interactive      := e.interactive
    grindOnly        := e.grindOnly
    hasSorry         := e.hasSorry
    activated        := e.activated.toList
    used             := e.used.toList
    coverageGap      := e.coverageGap
    isPrivate        := e.isPrivate }

/-- Per-file in-proof grind timeout (ms). See `grindFileTimeoutMs`. -/
def grindInProofFileTimeoutMs : Nat := 600000

/-- Drive every discovered file through the frontend and collect
`GrindInProofRecord`s plus the merged env-wide `available` hint set. Per-file errors
are logged and skipped (one bad file never aborts the run).

`unsafe` because in-process elaboration runs imported modules' interpreted
`initialize` code (see `Frontend.elaborateFile`). -/
unsafe def extractGrindInProofViaFrontend (files : Array Discover.DiscoveredFile)
    (includePrivate : Bool)
    : IO (Array GrindInProofRecord × Array String × FileDriver.FileStats) := do
  let deadlineMs := FileDriver.deadlineFor grindInProofFileTimeoutMs
  let (results, stats) ← FileDriver.driveFiles files
    (collect := fun r => grindInProofCore r includePrivate deadlineMs)
    (outcomeOf := (some ·.outcome))
  let recs := results.flatMap fun fr =>
    fr.entries.map fun e => grindInProofEntryToRecord e fr.file.relPath
  return (recs, mergeHints (results.map (·.extra)), stats)

end Corpus
