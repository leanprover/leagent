/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Corpus.CollectCommon
import Corpus.SourceSyntax

/-!
`Corpus.ProofMetrics` — proof-complexity metrics for the regular corpus record,
enabled by `--proof-metrics`.

# Why

The regular record has two whole-proof representations (`body`, and with
`--reverse-elab` the `proof_script`) and dependency cones (`deps`/`premises`), but
no measure of how big or how intricate a proof *is*. This module derives that
measure so a consumer can estimate proof complexity — and, downstream in Aurora,
down-sample by it — WITHOUT joining against the `--proof-states` dataset. Every
value here is a scalar or a small array, so the schema stays one wide flat table.

# The two families (documented once, here, and mirrored on `ConstRecord`)

The metrics split into two families that MUST NOT be conflated, because they
measure different things and are populated on different rows:

1. **Tactic family** — computed from the AUTHOR'S proof SYNTAX (the `by` block),
   never from the elaborated term. It measures the human-written tactic script:
   step counts, nesting depth, which tactics were used, how many rewrites /
   case-splits / intermediate `have`s. This is `none`/`#[]` for a TERM-mode proof
   (`:= rfl`, `:= fun …`) — there is no author tactic script to measure. The
   `isTermProof` flag is what makes those nulls interpretable: `true` means "not a
   tactic proof", not "a zero-step tactic proof".

2. **Semantic family** — computed from the elaborated proof `Expr` (in
   `CorpusManifest.buildEntry`, not here): `proofTermSize` / `proofTermDepth`.
   Populated for EVERY theorem including term-mode ones, so it is the complexity
   signal for the rows the tactic family leaves null.

Provenance never blurs: tactic family = what the author wrote in tactic mode;
semantic family = the elaborated term, always present. Reverse-elaboration
(`--reverse-elab`) is orthogonal — it only fills `proof_script`/`proof_method`,
and the metrics here are byte-identical with or without it.

# Why syntax, not the InfoTree

`--proof-states` walks the InfoTree and renders every goal, which is bounded by a
step ceiling (`ProofStates.stepCeiling`) precisely because rendering is the cost
centre. The tactic family needs none of that — counting syntax nodes is O(tree)
and allocates nothing per node — so it has NO ceiling and reports honest numbers
for exactly the large, intricate proofs a complexity estimate cares most about.
It reuses `CollectCommon.tacticKindSet` (the parser-category selection test) so it
agrees with the proof-states walk on what counts as a tactic.
-/

namespace Corpus.ProofMetrics

open Lean
open Corpus.SourceSyntax

/-! ## Tactic classification

Which authored tactics count as case-splits, rewrites, intermediate assertions, or
automation. Keyed by `SyntaxNodeKind` string, because the target project's tactics
(and Mathlib's `aesop`/`linarith`/…, absent from core) are known only by kind name
at extraction time. Matching the STRING rather than a `` `kind `` literal is what
lets this recognize a Mathlib tactic without the extractor depending on Mathlib. -/

/-- Tactic kinds that introduce a case analysis (one goal becomes several). -/
def caseSplitKinds : List String :=
  [``Lean.Parser.Tactic.induction, ``Lean.Parser.Tactic.cases,
   ``Lean.Parser.Tactic.rcases, ``Lean.Parser.Tactic.obtain,
   ``Lean.Parser.Tactic.match, ``Lean.Parser.Tactic.split].map toString
  ++ ["«tacticBy_cases_:_»"]

/-- Tactic kinds that rewrite the goal by equalities. `simp`/`simp_all` are
counted as automation, not rewrites — they do far more than a directed rewrite. -/
def rewriteKinds : List String :=
  [``Lean.Parser.Tactic.rwSeq, ``Lean.Parser.Tactic.rewriteSeq].map toString

/-- Tactic kinds that introduce a named intermediate fact into the context. -/
def haveKinds : List String :=
  [``Lean.Parser.Tactic.tacticHave__, ``Lean.Parser.Tactic.tacticSuffices_,
   ``Lean.Parser.Tactic.tacticLet__].map toString

/-- The kind of a `calc` block. Its steps are counted separately (`calcSteps`). -/
def calcKind : String := toString ``Lean.calcTactic

/-- The kind of a single `calc` step (`_ = c := …`), the unit `calcSteps` counts. -/
def calcStepKind : String := toString ``Lean.calcStep

/-- Automation tactics: a single one can discharge a goal that would otherwise be
many manual steps, so their PRESENCE is a strong complexity signal on its own.
Reported as the sorted set that appears (`automationTactics`), not just a count.

The value is the SHORT, stable tactic name (`simp`, `omega`, `aesop`) rather than
the syntax-kind string, so the column reads the way a user thinks of the tactic
and is comparable across the core/Mathlib kind-naming differences. -/
def automationKinds : List (String × String) :=
  [(toString ``Lean.Parser.Tactic.simp,           "simp"),
   (toString ``Lean.Parser.Tactic.simpAll,        "simp_all"),
   (toString ``Lean.Parser.Tactic.omega,          "omega"),
   (toString ``Lean.Parser.Tactic.decide,         "decide"),
   (toString ``Lean.Parser.Tactic.grind,          "grind"),
   -- Mathlib tactics: matched by kind string so no dependency is needed. The
   -- kind names are stable (`Mathlib.Tactic.<Name>` / `<name>` leading nodes).
   ("Aesop.Frontend.Parser.aesopTactic",           "aesop"),
   ("Mathlib.Tactic.tacticLinarith___",            "linarith"),
   ("Mathlib.Tactic.tacticNlinarith___",           "nlinarith"),
   ("Mathlib.Tactic.NormNum.normNum",              "norm_num"),
   ("Mathlib.Tactic.Tauto.tacticTauto_",           "tauto"),
   ("Mathlib.Tactic.tacticPolyrith",               "polyrith"),
   ("Mathlib.Tactic.tacticField_simp__",           "field_simp")]

/-! ## The metric record

The tactic-family half of one theorem's metrics. The semantic half
(`proofTermSize`/`proofTermDepth`) is attached by `CorpusManifest.buildEntry`,
which holds the elaborated `Expr`; keeping this record syntax-only makes the whole
module pure and unit-testable without an `Environment`. -/

/-- The tactic-family metrics for one proof, plus `attributes`. Every field is
`none`/`#[]` for a term-mode proof except `isTermProof := true` and `attributes`
(which come from the declaration modifiers regardless of proof form). -/
structure TacticMetrics where
  /-- `true` iff the proof is a bare term (`:= …`, no `by`). When `true`, every
  other tactic-family field is `none`/`#[]` by construction. -/
  isTermProof     : Bool
  /-- Top-level tactic steps (the immediate children of the proof's tactic
  sequence). `none` for a term proof. -/
  tacticStepCount : Option Nat
  /-- Every author tactic, nested children included. `none` for a term proof. -/
  tacticTotalCount : Option Nat
  /-- Deepest tactic nesting (0 for a flat proof). `none` for a term proof. -/
  maxTacticDepth  : Option Nat
  /-- Sorted distinct tactic-kind strings present. `#[]` for a term proof. -/
  tacticKinds     : Array String
  /-- Kind string → occurrence count, for the whole tree. `#[]` for a term proof. -/
  tacticHistogram : Array (String × Nat)
  /-- Case-analysis tactics (`caseSplitKinds`). `none` for a term proof. -/
  caseSplitCount  : Option Nat
  /-- Directed rewrites (`rewriteKinds`). `none` for a term proof. -/
  rewriteCount    : Option Nat
  /-- Intermediate assertions (`haveKinds`). `none` for a term proof. -/
  haveCount       : Option Nat
  /-- Steps inside `calc` blocks (`calcStepKind`). `none` for a term proof. -/
  calcSteps       : Option Nat
  /-- Sorted short names of automation tactics that appear (`automationKinds`).
  `#[]` for a term proof OR a manual proof with no automation. -/
  automationTactics : Array String
  /-- Attribute names on the declaration (`@[simp]` → `"simp"`), sorted. Read from
  the declaration modifiers, so present for term and tactic proofs alike. -/
  attributes      : Array String
  deriving Inhabited, Repr

/-- The metrics of a proof that is a bare term: everything null but the flag, plus
whatever `attributes` the caller found on the declaration. -/
def TacticMetrics.termProof (attributes : Array String) : TacticMetrics :=
  { isTermProof := true, tacticStepCount := none, tacticTotalCount := none
    maxTacticDepth := none, tacticKinds := #[], tacticHistogram := #[]
    caseSplitCount := none, rewriteCount := none, haveCount := none
    calcSteps := none, automationTactics := #[], attributes }

/-! ## Walking the proof syntax

The proof body is a `Syntax` tree mixing author tactics with structural glue
(`tacticSeq`, `«tactic_<;>_»`, `paren`, `cdot`, atoms). `tacticKindSet` selects the
author tactics; everything else is descended THROUGH, so a tactic nested inside a
combinator (`simp <;> omega`, `· exact h`) is counted at the depth of the nearest
enclosing author tactic — exactly the reparenting `ProofStates.walkTree` does on
the InfoTree, but here on raw syntax. -/

/-- A visitor folded over the kept-tactic forest: `depth` is the current author
tactic nesting, `f` sees every kept node with its depth. Structural nodes advance
the walk without incrementing depth or invoking `f`. -/
private partial def foldTactics {α} (kinds : Std.HashSet Name) (stx : Syntax)
    (depth : Nat) (init : α) (f : α → Syntax → Nat → α) : α :=
  let kept := kinds.contains stx.getKind
  let init := if kept then f init stx depth else init
  let childDepth := if kept then depth + 1 else depth
  match stx with
  | .node _ _ args => args.foldl (fun acc a => foldTactics kinds a childDepth acc f) init
  | _              => init

/-- Immediate kept-tactic children: the top-level steps. A step is "top-level"
when no kept tactic encloses it — i.e. depth 0 in `foldTactics`. -/
private def topLevelCount (kinds : Std.HashSet Name) (proof : Syntax) : Nat :=
  foldTactics kinds proof 0 0 (fun n _ d => if d == 0 then n + 1 else n)

/-- The mutable tally the single fold over the proof accumulates. -/
private structure Tally where
  hist       : Std.HashMap String Nat := {}
  total      : Nat := 0
  maxDepth   : Nat := 0
  caseSplits : Nat := 0
  rewrites   : Nat := 0
  haves      : Nat := 0
  autos      : Std.HashSet String := {}
  deriving Inhabited

/-- Count nodes of one exact kind string anywhere in `stx`. -/
private partial def countByKind (stx : Syntax) (kind : String) : Nat :=
  let here := if stx.getKind.toString == kind then 1 else 0
  match stx with
  | .node _ _ args => args.foldl (fun n a => n + countByKind a kind) here
  | _              => here

/-- Analyze the proof syntax `proof` (the `declVal`/`by`-block node) into the
tactic family. `kinds` is `CollectCommon.tacticKindSet`. -/
def analyzeTacticProof (kinds : Std.HashSet Name) (proof : Syntax)
    (attributes : Array String) : TacticMetrics :=
  -- Tally kinds, depth, and the recognized categories in ONE fold over the kept
  -- author tactics.
  let t : Tally := foldTactics kinds proof 0 {} fun t stx d =>
    let k := stx.getKind.toString
    { hist       := t.hist.insert k (t.hist.getD k 0 + 1)
      total      := t.total + 1
      maxDepth   := Nat.max t.maxDepth d
      caseSplits := if caseSplitKinds.contains k then t.caseSplits + 1 else t.caseSplits
      rewrites   := if rewriteKinds.contains k then t.rewrites + 1 else t.rewrites
      haves      := if haveKinds.contains k then t.haves + 1 else t.haves
      autos      := match automationKinds.find? (·.1 == k) with
                    | some (_, name) => t.autos.insert name
                    | none           => t.autos }
  -- `calcStep`/`calcStepKind` is NOT in the tactic category (they are the inner
  -- steps of a `calc` block, not tactics), so count them with a separate pass —
  -- one per `_ = c := …` line; the `calcFirstStep` is the initial relation, not a
  -- step.
  let kindsSorted := (t.hist.toList.map (·.1)).toArray.qsort (· < ·)
  let histSorted  := (t.hist.toList.mergeSort (fun a b => a.1 < b.1)).toArray
  let autosSorted := (t.autos.toList.mergeSort (· < ·)).toArray
  { isTermProof := false
    tacticStepCount  := some (topLevelCount kinds proof)
    tacticTotalCount := some t.total
    maxTacticDepth   := some t.maxDepth
    tacticKinds      := kindsSorted
    tacticHistogram  := histSorted
    caseSplitCount   := some t.caseSplits
    rewriteCount     := some t.rewrites
    haveCount        := some t.haves
    calcSteps        := some (countByKind proof calcStepKind)
    automationTactics := autosSorted
    attributes }

/-! ## Attributes

`@[simp, reducible]` on a declaration is a `Command.declModifiers` node holding a
`Term.attributes` block of `Term.attrInstance`s. The attribute NAME is the leading
identifier of each instance (`Attr.simp "simp" …`, `Attr.simple `reducible …`), so
harvesting the first identifier/atom token of each `attrInstance` recovers the
names the way a reader sees them. -/

/-- Attribute names attached to the declaration command `cmdStx`, sorted and
deduped. `#[]` when the declaration has no `@[…]` block. -/
partial def attributesOf (cmdStx : Syntax) : Array String := Id.run do
  let some attrs := findByKind cmdStx [``Lean.Parser.Term.attributes] | return #[]
  let mut names : Array String := #[]
  for inst in collectByKind attrs [``Lean.Parser.Term.attrInstance] do
    -- The attribute name is the first identifier/atom leaf under the instance,
    -- past the (usually empty) `attrKind`. `firstName?` finds it.
    if let some n := firstName? inst then
      unless names.contains n do names := names.push n
  return names.qsort (· < ·)
where
  /-- Collect all nodes of a kind (pre-order), like `CorpusManifest.collectByKind`
  but local so this module stays self-contained. -/
  collectByKind (stx : Syntax) (kinds : List SyntaxNodeKind)
      (acc : Array Syntax := #[]) : Array Syntax :=
    let acc := if kinds.contains stx.getKind then acc.push stx else acc
    match stx with
    | .node _ _ args => args.foldl (fun acc a => collectByKind a kinds acc) acc
    | _              => acc
  /-- The first identifier or keyword atom under `stx` — the attribute's name. An
  `attrKind` (the optional `scoped`/`local`) is skipped because it holds no name
  leaf when empty; when non-empty its keyword would sort before the real name, so
  we take the LAST such token per instance instead. Simpler and correct here: the
  attribute name is always the first NON-`attrKind` name token, and `attrKind`
  contributes none when empty (the common case), so first-token works. -/
  firstName? (stx : Syntax) : Option String :=
    match stx with
    | .ident _ _ n _ =>
        -- Strip macro-scope hygiene so `reducible._@…` reads as `reducible`.
        some n.eraseMacroScopes.toString
    | .atom _ s      => if s.isEmpty then none else some s
    | .node _ _ args => args.findSome? firstName?
    | _              => none

/-! ## Per-declaration entry point

The corpus collector holds each declaration's command `Syntax`; this turns one such
command into its tactic-family metrics. Term-vs-tactic is decided by whether the
value contains a `by` block anywhere (`Term.byTactic`): a proof with no `by` is a
term proof and gets the null tactic family. The whole declaration value is handed
to `analyzeTacticProof`, so equation-clause and `where` proofs — whose tactics are
nested in alternatives — are still counted, since the walk reparents through every
structural node. -/

/-- The tactic-family metrics + attributes for one declaration command. `kinds` is
`CollectCommon.tacticKindSet`. A declaration whose value has no `by` block is a term
proof (null tactic family); attributes are read regardless. -/
def metricsForCommand (kinds : Std.HashSet Name) (cmdStx : Syntax) : TacticMetrics :=
  let attrs := attributesOf cmdStx
  match declarationValue? cmdStx with
  | none => TacticMetrics.termProof attrs
  | some (_, value) =>
    match findByKind value [``Lean.Parser.Term.byTactic] with
    | some byNode => analyzeTacticProof kinds byNode attrs
    | none        => TacticMetrics.termProof attrs

/-- Map each declaration's key position to its tactic-family metrics, keyed the way
`CorpusManifest.buildSourceMap` keys (by `findDeclarationRanges?` selection
position) so a constant looks up its own proof metrics. Only built under
`--proof-metrics`. -/
def buildMetricsMap (kinds : Std.HashSet Name) (source : String)
    (commands : Array Syntax) : Std.HashMap (Nat × Nat) TacticMetrics := Id.run do
  let fileMap := source.toFileMap
  let mut m : Std.HashMap (Nat × Nat) TacticMetrics := {}
  for cmdStx in commands do
    if (declarationId? cmdStx).isSome then
      let metrics := metricsForCommand kinds cmdStx
      for key in declarationKeys fileMap cmdStx do
        m := m.insert key metrics
  return m

end Corpus.ProofMetrics
