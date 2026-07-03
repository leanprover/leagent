import Lean
import Corpus.Records
import Corpus.Discover
import Corpus.Frontend
import Corpus.GrindInProof

/-!
Frontend-driven in-proof grind extraction: the in-process observation-mode collector.

Parallel to `Corpus.GrindExtract`, but runs the in-proof grind collector
(`grindInProofCore`) instead of the whole-statement one. For each source file it
elaborates the file in-process (`Frontend.elaborateFile`) then asks the collector
to walk the file's `InfoTree`s for every `grind` CALL SITE inside a proof, re-run
instrumented grind on each restored subgoal (with the author's hints), and report
the triple + artifacts. Each `GrindInProofEntry` becomes a `GrindInProofRecord`
(adding the `file` path from discovery). The env-wide `available` hint set is
merged into one set by the caller.

See `Corpus.GrindExtract` for the shared cooperative-bounding rationale (per-goal
`grindHeartbeats` + per-file `grindDeadlineMs`).
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

/-- Summary of an in-proof grind-extraction run. File-level counters plus
per-call-site outcome counts. -/
structure GrindInProofRunStats where
  filesTotal   : Nat := 0
  filesOk      : Nat := 0
  filesEmpty   : Nat := 0  -- elaborated but produced 0 grind call sites
  filesError   : Nat := 0
  closed       : Nat := 0  -- call sites grind closed
  stuck        : Nat := 0  -- grind ran but could not close
  errored      : Nat := 0  -- grind threw / site skipped
  skipped      : Nat := 0  -- past the per-file deadline
  deriving Inhabited

/-- Per-file in-proof grind timeout (ms). See `GrindExtract.grindFileTimeoutMs`. -/
def grindInProofFileTimeoutMs : Nat := 600000

/-- Drive every discovered file through the frontend (in parallel) and collect
`GrindInProofRecord`s plus the merged env-wide `available` hint set. Per-file
errors are logged to stderr and skipped (one bad file never aborts the run).

`unsafe` because in-process elaboration runs imported modules' interpreted
`initialize` code (see `Frontend.elaborateFile`). -/
unsafe def extractGrindInProofViaWorkers (projectRoot : System.FilePath)
    (files : Array Discover.DiscoveredFile) (includePrivate : Bool)
    : IO (Array GrindInProofRecord × Array String × GrindInProofRunStats) := do
  let _ := projectRoot  -- parity with the old signature; discovery already resolved paths
  Frontend.initFrontend
  let grindDeadlineMs := grindInProofFileTimeoutMs * 4 / 5
  let results ← Frontend.elaborateFiles files fun importLock df => do
    let r ← Frontend.elaborateFile importLock df
    let (avail, entries) ← grindInProofCore r includePrivate grindDeadlineMs
    pure (df, avail, entries)
  let mut recs      : Array GrindInProofRecord := #[]
  let mut available : Std.HashSet String := {}
  let mut stats     : GrindInProofRunStats := { filesTotal := files.size }
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
        recs := recs.push (grindInProofEntryToRecord e df.relPath)
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
