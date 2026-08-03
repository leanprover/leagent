import Lean
import Corpus.Records
import Corpus.Discover
import Corpus.Frontend
import Corpus.FileDriver
import Corpus.GrindManifest

/-!
Frontend-driven grind-manifest extraction: the AlphaGrind data collector.

Runs the grind collector (`grindManifestCore`) over each elaborated file, asking it
to RE-PROVE every theorem with `grind`'s default strategy and report what grind did.
Each `GrindManifestEntry` becomes a `GrindGoalRecord` (adding the `file` path from
discovery); the per-file `available` hint sets are merged into one env-wide set.

The per-goal `grindHeartbeats` backstop (in `Corpus.GrindManifest`) bounds each grind
run cooperatively, and the per-file deadline sheds the expensive tail.

The driving, per-file error containment, and file/outcome counting are shared with
the other modes via `Corpus.FileDriver.driveFiles`.
-/

namespace Corpus

open Lean

/-- Map one `GrindManifestEntry` to a `GrindGoalRecord`. `relFile` is the
project-relative source path from discovery. `sourceUsesGrind` is a best-effort
flag supplied by the caller (currently always `false`; per-theorem source mining
is a later pass). -/
def grindEntryToRecord (e : GrindManifestEntry) (relFile : String)
    (sourceUsesGrind : Bool := false) : GrindGoalRecord :=
  { name            := e.name
    module          := e.module
    file            := some relFile
    startLine       := e.startLine
    goalType        := e.goalType
    outcome         := e.outcome
    interactive     := e.interactive
    grindOnly       := e.grindOnly
    hasSorry        := e.hasSorry
    activated       := e.activated.toList
    used            := e.used.toList
    coverageGap     := e.coverageGap
    isPrivate       := e.isPrivate
    sourceUsesGrind := sourceUsesGrind }

/-- Per-file grind timeout (ms). The fold bounds itself with 80% of this
(`FileDriver.deadlineFor`), cheap-first with the tail shed to `deadline_skipped`. -/
def grindFileTimeoutMs : Nat := 600000

/-- The outcome labels the grind run summary reports individually; anything else is
counted as an error. Shared with the in-proof mode. -/
def grindOutcomeLabels : List String :=
  [Outcome.closed, Outcome.stuck, Outcome.deadlineSkipped]

/-- Merge per-file hint sets into one sorted env-wide set. -/
def mergeHints (perFile : Array (Array String)) : Array String := Id.run do
  let mut merged : Std.HashSet String := {}
  for hints in perFile do
    for h in hints do
      merged := merged.insert h
  return (merged.toList.mergeSort (· < ·)).toArray

/-- Drive every discovered file through the frontend and collect `GrindGoalRecord`s
plus the merged env-wide `available` hint set. Per-file errors are logged and
skipped (one bad file never aborts the run).

`unsafe` because in-process elaboration runs imported modules' interpreted
`initialize` code (see `Frontend.elaborateFile`). -/
unsafe def extractGrindViaFrontend (files : Array Discover.DiscoveredFile)
    (includePrivate : Bool)
    : IO (Array GrindGoalRecord × Array String × FileDriver.FileStats) := do
  let deadlineMs := FileDriver.deadlineFor grindFileTimeoutMs
  let (results, stats) ← FileDriver.driveFiles files
    (collect := fun r => grindManifestCore r includePrivate deadlineMs)
    (outcomeOf := (some ·.outcome))
  let recs := results.flatMap fun fr =>
    fr.entries.map fun e => grindEntryToRecord e fr.file.relPath
  return (recs, mergeHints (results.map (·.extra)), stats)

end Corpus
