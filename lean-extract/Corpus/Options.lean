/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
`Corpus.Options` — the per-file collection knobs, as one value.

These five settings decide what a collector emits for one file. They are chosen once
from the command line and then travel together through every layer: the CLI, the
driver, the isolated child process, the collector fold, and the per-constant builder.

Passing them as ONE record rather than five positional arguments is what keeps that
chain readable — and, because the record carries `ToJson`/`FromJson`, it is also what
crosses the isolated-child process boundary. That boundary previously used a
hand-written flag encoder on one side and a hand-written flag parser on the other;
keeping two encodings of the same five fields in agreement is exactly the kind of
thing that silently breaks (see the arg-parity bug documented in
`Corpus.Reexec.reexecUnderLake`). With one serializable record there is one encoding.

## On the strictness of the derived decoder

Lean's derived `FromJson` is all-or-nothing: it requires EVERY field to be present,
ignoring the field defaults above. That is safe here only because the child is the
SAME executable as the parent (`IO.appPath`), so encoder and decoder are always the
same version — a payload is never read by a different build than wrote it. (The
resume fingerprint hashes the executable for the same reason.) If this record ever
has to be read by another process or persisted across versions, that assumption
breaks and the decode needs per-field defaults.
-/

namespace Corpus

open Lean

/-! ## Outcome labels

An entry's `outcome` is a string on the wire (it is a dataset field), so the tally is
keyed by string. But a bare literal at each use site is a silent-failure hazard: a
misspelled key in a lookup returns 0 rather than failing to compile. These constants
are therefore the ONLY place each label is written; producers set them and the run
summaries look them up through the same identifier.
-/

namespace Outcome

/-- Grind closed the goal. -/
def closed : String := "closed"
/-- Grind ran but did not close the goal. -/
def stuck : String := "stuck"
/-- Past the per-file budget, so the item was not attempted. -/
def deadlineSkipped : String := "deadline_skipped"
/-- The item exceeded a size ceiling and was deliberately not attempted. -/
def skippedLarge : String := "skipped_large"
/-- Captured successfully (proof states). -/
def ok : String := "ok"
/-- The collector threw on this item. -/
def error : String := "error"

end Outcome

/-- What a collector should emit for one file. -/
structure CollectOptions where
  /-- Emit compiler-internal / auto-generated names (constructors, recursors,
  `.casesOn`, projections, `._proof_*`, …). CLI: `--include-internal`. -/
  includeInternal : Bool := false
  /-- Emit declarations marked `private`. CLI: `--no-private` (inverted). -/
  includePrivate  : Bool := true
  /-- Reverse-elaborate each theorem's proof term into a verified tactic script.
  Off by default: it re-elaborates every proof. CLI: `--reverse-elab`. -/
  reverseElab     : Bool := false
  /-- With `reverseElab`, also try goal-closing tactics (`simp`/`omega`/…).
  Substantially slower. CLI: `--closers`. -/
  reverseClosers  : Bool := false
  /-- Theorem names to skip reverse-elaboration for, matched against either the
  corpus display name or the raw Lean internal name. CLI: `--skip-reverse`. -/
  reverseSkip     : Array String := #[]
  /-- Emit proof-complexity metric columns on each record (tactic-family syntactic
  metrics, semantic proof-term size/depth, and declaration attributes). Off by
  default: it walks each proof's syntax and sizes each proof term. Independent of
  `reverseElab` — the metric columns are identical with or without it. CLI:
  `--proof-metrics`. See `Corpus.ProofMetrics`. -/
  proofMetrics    : Bool := false
  deriving Inhabited, ToJson, FromJson

end Corpus
