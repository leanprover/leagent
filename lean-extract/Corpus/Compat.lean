/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean

/-!
Toolchain-compatibility shims.

The extractor reads `grind`'s INTERNAL state to recover which lemmas a successful
grind run actually used (`Corpus.GrindManifest`). That state moved in v4.31.0, so
this module carries the version predicate and the handful of gated expressions
that let the package compile on older toolchains.

# What changed in v4.31.0

Three related additions, all landing together:

* `Lean.Grind.Config.markInstances` — the flag that asks grind to tag E-matching
  proofs with instance IDs. Does not exist pre-4.31.
* `Lean.Meta.Grind.State.instanceMap` — the id→theorem map. Pre-4.31 the map
  exists only as `EMatch.SearchState.instanceMap`, which is search-LOCAL: it is
  discarded when the E-matching search ends, so by the time the collector reads
  the result there is nothing left to read. v4.31.0 lifts it onto the outer
  `Grind.State`, populated behind the `markInstances` gate.
* `Lean.Elab.Tactic.grind.unusedLemmaThreshold` — the option whose guard the real
  tactic uses to decide whether to request instance marking.

So this is not a rename that a shim can paper over: pre-4.31 the used-lemma data
is genuinely unreachable from where the collector runs. Consequently the gate
below makes the package COMPILE everywhere but the grind modes REFUSE TO RUN
below 4.31 (see `Corpus.grindSupported` and its callers in `Corpus.Main`), rather
than emitting records with an empty `used` list. `GrindGoalRecord.used` is a
plain `List String`, so a degraded run would be indistinguishable from "grind
used no lemmas" — silently wrong training data, which is worse than no data.

# The mechanism

Lean has no preprocessor, but an unexpanded macro branch is never elaborated, so
a `macro` that chooses a branch from `Lean.version` may reference fields absent
on the running toolchain in the branch it discards. That is what `gatedGrind`
below relies on; the pre-4.31 branches are what the compiler sees there.
-/

namespace Corpus

open Lean

/-- `true` when the running toolchain is v4.31.0 or newer, i.e. when grind's
used-lemma data is reachable. Evaluated at ELABORATION time (it reads
`Lean.version`, a compile-time constant of the compiling toolchain), so it is
also what the `gatedGrind` macro branches on. -/
def grindSupported : Bool :=
  Lean.version.major > 4 || (Lean.version.major == 4 && Lean.version.minor ≥ 31)

/-- Stable marker embedded in `grindUnsupportedMsg`, for callers that need to
recognise this specific refusal rather than any failure — CI asserts the gate
fires by grepping for it.

Separate from the prose because matching on a sentence is too fragile: CI first
grepped for "requires Lean v4.31.0 or newer" against a message that says
"require" (plural subject — two flags are listed), so the assertion failed on
exactly the toolchains the gate was working correctly on. Change the wording
above freely; keep this token, or update both together. -/
def grindUnsupportedMarker : String := "grind-unsupported-toolchain"

/-- Human-readable refusal used by the grind CLI modes on old toolchains. Carries
`grindUnsupportedMarker` so the reason is machine-checkable. -/
def grindUnsupportedMsg : String :=
  s!"[{grindUnsupportedMarker}] --grind-manifest and --grind-in-proof require \
Lean v4.31.0 or newer \
(running v{Lean.version.major}.{Lean.version.minor}.{Lean.version.patch}): \
grind's used-lemma data (Grind.State.instanceMap, Config.markInstances) was \
only exposed in v4.31.0. Re-run on a v4.31+ toolchain; the other extraction \
modes work on this one."

open Lean Elab in
/-- `gatedGrind a else b` elaborates `a` on v4.31+ and `b` otherwise.

The discarded branch is never elaborated, which is the whole point: `a` may
mention `markInstances` / `instanceMap` / `unusedLemmaThreshold`, none of which
resolve pre-4.31. Keep both branches to single expressions — this is a
compatibility seam, not a place for logic. -/
macro "gatedGrind " a:term " else " b:term : term => do
  if grindSupported then return a else return b

end Corpus
