/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean
import Lean.Util.CollectAxioms
import Corpus.Frontend
import Corpus.CollectCommon

/-!
`Corpus.Verify` — the shared VERIFICATION MECHANISM that core extraction and the
enrichment passes (reverse-elab, grind) both build on.

The architecture is: CORE extraction produces the ground-truth records; the
ENRICHMENT passes (reverse-elaboration, grind data collection) are *clients* that
must first rebuild an environment containing the VERIFIED theorem, then fill in
their extra fields against that env. Making "rebuild a verified environment" one
primitive means an enrichment failure can never be confused with a broken
environment: a client only ever runs over a constant we have already confirmed is
present in the file's real post-elaboration env and is `sorry`-free.

## What "verified" means here

The cheapest CORRECT way to obtain "an environment containing the checked
theorem" is NOT to reassemble the statement from record text and re-elaborate it
(that is a separate, harder goal — text self-containment — pursued elsewhere). It
is to re-elaborate the ORIGINAL source file with `Frontend.elaborateFile`: the
frontend runs the real `addDecl`, so every constant in the resulting env has
already passed the kernel in its true context. Verification then reduces to two
cheap post-hoc checks per constant:

  * PRESENT — the name resolves in `env` (elaboration did not silently drop it).
  * SORRY-FREE — `collectAxioms name` does not contain `sorryAx` (the proof is
    real, not a `sorry`/`admit` placeholder that the kernel still accepts).

`VerifiedConst` bundles the constant with these facts so a client never
re-derives them. `foldVerifiedFileConstants` batches by FILE — elaborate once,
run the client over all of the file's verified user constants — so enrichment
never pays a per-record re-elaboration cost.
-/

namespace Corpus.Verify

open Lean

/-- A file-local constant read out of the file's real post-elaboration
environment, carrying the two verification facts an enrichment client may want.
It is a *query surface*, NOT a gate: `collectFileConstants` returns one of these
for EVERY file-local user constant (including `sorry`-laced ones), and each client
decides whether to act on `isSorryFree`. That keeps the substrate faithful — the
corpus base pass emits `sorry` theorems (with `has_sorry := true`), so dropping
them here would silently change its record set. -/
structure VerifiedConst where
  /-- The constant's info, as it exists in the verified environment. -/
  info        : ConstantInfo
  /-- `collectAxioms info.name`, sorted — the transitive axiom set. Exposed so a
  client can reuse it (e.g. the corpus schema's `axioms` field) without recomputing. -/
  axioms      : Array Name
  /-- `false` iff `axioms` contains `sorryAx` — i.e. the proof is real, not a
  `sorry`/`admit` placeholder the kernel still accepts. A client that wants to
  operate only over genuinely-proved theorems (e.g. reverse-elab learning targets)
  filters on this. -/
  isSorryFree : Bool
  deriving Inhabited

/-- Does `name`'s transitive axiom set contain `sorryAx`? A `sorry`/`admit` in the
proof shows up here even though the kernel still accepts the declaration. -/
def hasSorryAxiom (axioms : Array Name) : Bool :=
  axioms.contains ``sorryAx

/-- Read the verification facts for one file-local constant: its (sorted) axiom
set and whether it is `sorry`-free. The PRESENT check is implicit — we are handed
a `ConstantInfo` that we just read out of `env`, so the declaration exists and
passed the kernel in its true elaboration context. -/
def verifyConst (name : Name) (info : ConstantInfo) : CoreM VerifiedConst := do
  let axioms := (← Lean.collectAxioms name).qsort (toString · < toString ·)
  return { info, axioms, isSorryFree := !hasSorryAxiom axioms }

/-- Enumerate every file-local user constant in the ambient environment — in
`env.constants` iteration order — with its verification facts attached. Runs in
ANY `CoreM` (typically already inside a collector's `Frontend.runCollectorOn`
context), so a fold can obtain verified constants WITHOUT a second elaboration.

"File-local user constant" is `CollectCommon.isUserConstant` (introduced by the
elaborated file, not an internal-detail name) — exactly the set the corpus/grind
folds iterate. This is the shared enrichment SUBSTRATE: a client (reverse-elab,
grind) iterates these instead of re-enumerating `env.constants` and re-deriving
`sorry`-freedom / axioms itself. -/
def verifiedFileConstants : CoreM (Array VerifiedConst) := do
  let env ← getEnv
  let mut out : Array VerifiedConst := #[]
  for (name, info) in env.constants.toList do
    if CollectCommon.isUserConstant env name then
      out := out.push (← verifyConst name info)
  return out

/-- `verifiedFileConstants` for an already-elaborated file: establishes the file's
real `CoreM` context (`Frontend.runCollectorOn`) and enumerates its verified
constants. The `IO`-level entry point for a standalone enrichment pass. -/
def collectFileConstants (r : Frontend.ElabResult) : IO (Array VerifiedConst) :=
  Frontend.runCollectorOn r verifiedFileConstants

end Corpus.Verify
