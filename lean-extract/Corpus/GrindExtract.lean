import Lean
import Corpus.Records
import Corpus.Discover
import Corpus.Frontend
import Corpus.GrindManifest

/-!
Frontend-driven grind-manifest extraction: the in-process AlphaGrind data collector.

Parallel to `Corpus.WorkerExtract`, but runs the grind collector
(`grindManifestCore`) instead of the corpus collector. For each source file it
elaborates the file in-process (`Frontend.elaborateFile`) then asks the collector
to RE-PROVE every theorem with `grind`'s default strategy and report what grind
did. Each `GrindManifestEntry` becomes a `GrindGoalRecord` (adding the `file` path
from discovery). The file-level `available` hint set is merged into a single
env-wide set by the caller.

The per-goal `grindHeartbeats` backstop (in `Corpus.GrindManifest`) bounds each
grind run cooperatively, and the per-file `grindDeadlineMs` sheds the expensive
tail — together the in-process substitute for the killable worker. The
`extractGrind*` names are kept for source compatibility with `Main.lean`.
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

/-- Summary of a grind-extraction run. -/
structure GrindRunStats where
  filesTotal   : Nat := 0
  filesOk      : Nat := 0
  filesEmpty   : Nat := 0  -- elaborated but produced 0 grind records
  filesError   : Nat := 0
  closed       : Nat := 0  -- theorems grind closed
  stuck        : Nat := 0  -- grind ran but could not close
  errored      : Nat := 0  -- grind threw
  skipped      : Nat := 0  -- past the per-file deadline
  deriving Inhabited

/-- Per-file grind timeout (ms). The per-file fold bounds itself with
`grindDeadlineMs` set to 80% of this (cheap-first, tail-shed to
`deadline_skipped`); the 20% headroom is unused wall-clock slack now that there is
no request transport. -/
def grindFileTimeoutMs : Nat := 600000

/-- Drive every discovered file through the frontend (in parallel) and collect
`GrindGoalRecord`s plus the merged env-wide `available` hint set. Per-file errors
are logged to stderr and skipped (one bad file never aborts the run).

`unsafe` because in-process elaboration runs imported modules' interpreted
`initialize` code (see `Frontend.elaborateFile`). -/
unsafe def extractGrindViaWorkers (projectRoot : System.FilePath)
    (files : Array Discover.DiscoveredFile) (includePrivate : Bool)
    : IO (Array GrindGoalRecord × Array String × GrindRunStats) := do
  let _ := projectRoot  -- parity with the old signature; discovery already resolved paths
  Frontend.initFrontend
  let grindDeadlineMs := grindFileTimeoutMs * 4 / 5
  let results ← Frontend.elaborateFiles files fun importLock df => do
    let r ← Frontend.elaborateFile importLock df
    let (avail, entries) ← grindManifestCore r includePrivate grindDeadlineMs
    pure (df, avail, entries)
  let mut recs      : Array GrindGoalRecord := #[]
  let mut available : Std.HashSet String := {}
  let mut stats     : GrindRunStats := { filesTotal := files.size }
  for res in results do
    match res with
    | .ok (df, avail, entries) =>
      for a in avail do
        available := available.insert a
      if entries.isEmpty then
        stats := { stats with filesEmpty := stats.filesEmpty + 1 }
      else
        stats := { stats with filesOk := stats.filesOk + 1 }
      for e in entries do
        recs := recs.push (grindEntryToRecord e df.relPath)
        stats := match e.outcome with
          | "closed"           => { stats with closed  := stats.closed + 1 }
          | "stuck"            => { stats with stuck   := stats.stuck + 1 }
          | "deadline_skipped" => { stats with skipped := stats.skipped + 1 }
          | _                  => { stats with errored := stats.errored + 1 }
    | .error msg =>
      stats := { stats with filesError := stats.filesError + 1 }
      IO.eprintln s!"corpus-extract: {msg}"
  let availArr := (available.toList.mergeSort (· < ·)).toArray
  return (recs, availArr, stats)

end Corpus
