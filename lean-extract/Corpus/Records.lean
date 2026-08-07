import Lean

/-!
The on-wire record schema emitted by the corpus extractor.

One `ConstRecord` per Lean constant per JSONL line. Field order in the JSON
output is fixed by the explicit `mkObj` build below so consumers (e.g.,
HuggingFace datasets) get a stable schema.

JSON keys are emitted in `snake_case` (HF dataset convention); the in-memory
record uses Lean's idiomatic `camelCase`.
-/

namespace Corpus

open Lean

/-- One emitted constant. See module-level docstring for field semantics. -/
structure ConstRecord where
  name        : String
  kind        : String
  module      : String
  file        : Option String
  startLine   : Option Nat
  startCol    : Option Nat
  endLine     : Option Nat
  endCol      : Option Nat
  signature   : Option String
  body        : Option String
  /-- FULL source of the declaration command (doc + modifiers + signature + body),
  verbatim and re-elaboratable. Captured for every kind — including
  `inductive`/`structure`, whose `signature`/`body` are null. This is the text a
  self-contained record inlines for its owned `def`/`inductive`/`structure`
  dependencies. Null for constants with no source command. -/
  declSource  : Option String
  /-- Dotted enclosing namespace the declaration was elaborated under (e.g.
  `"LeanSQLite.Engine"`; empty at top level). The true declaring namespace, from
  the command-stack walk — not derivable from `name`. An assembled record wraps
  the (unqualified) `decl_source` under this namespace. -/
  declNamespace : String
  /-- Verbatim source of the scope commands active at the declaration, outermost
  first (`namespace`/`section` openers plus live `open`/`variable`/`universe`/
  `set_option`). Replaying these — then closing namespaces/sections — reproduces
  the declaration's elaboration scope in a standalone file. -/
  scopePrelude : List String
  /-- Direct imports of the declaration's file (dotted module names). A
  self-contained record imports the non-owned ones as its baseline and inlines the
  owned cone. Identical for every record from the same module. -/
  fileImports : List String
  type        : String
  value       : Option String
  /-- Mechanically reverse-elaborated tactic script (from the proof `Expr`),
  e.g. `by intro h; exact …`. Populated only for theorems when reverse
  elaboration is enabled (`--reverse-elab`); null otherwise. Every emitted
  script is verified to reproduce the original proof term up to defeq. -/
  proofScript : Option String
  /-- Which reverse-elaboration rung produced `proofScript`: `structural`
  (`cases`/`have`/`by_cases` decomposition), `rfl`, `exact`, `intro_rfl`,
  `intro_exact` (genuine decompositions), `*_opaque` (verified but the body is
  automation residue), `exact_whole` (verified but zero decomposition — one big
  `exact`), or `fail` (nothing verified). Null when reverse elaboration was not
  run. -/
  proofMethod : Option String
  doc         : Option String
  deps        : List String
  premises    : List String
  axioms      : List String
  isProtected : Bool
  isPrivate   : Bool
  tags        : List (String × String)
  -- Proof-complexity metrics (`--proof-metrics`). Populated only under that flag;
  -- every field below is its empty form (`none`/`[]`/`false`) otherwise, so the
  -- column set is stable whether or not the flag was passed. See
  -- `Corpus.ProofMetrics`.
  --
  -- The metrics split into two families that measure DIFFERENT things and are
  -- populated on different rows — do not conflate them:
  --   * Tactic family (`tacticStepCount` … `automationTactics`): a tactic script's
  --     shape. WHICH script depends on the run — the author's source `by` block on
  --     a plain run, the reverse-elaborated body on a `--reverse-elab` run.
  --     `tacticMetricsSource` names which per row. `none`/`[]` when there is no
  --     script to measure (a term-mode author proof on a plain run; a proof with no
  --     reverse-elab script on a `--reverse-elab` run). `isTermProof` always
  --     reports the ORIGINAL proof, so it disambiguates the nulls.
  --   * Semantic family (`proofTermSize`/`proofTermDepth`): from the elaborated
  --     proof term, so populated for EVERY theorem including term-mode ones — the
  --     complexity signal for the rows the tactic family leaves null. NOT affected
  --     by `--reverse-elab` (the reconstructed term is defeq to the original).
  /-- `true` iff the ORIGINAL proof is a bare term (`:= …`, no `by`), independent of
  `--reverse-elab`. On a plain run `true` forces the tactic family to `none`/`[]`
  (no author tactic script). On a `--reverse-elab` run a `true` row may still carry
  tactic metrics — measured from the SYNTHESIZED script — so pair this with
  `tacticMetricsSource` to read a row correctly. `false` for non-theorems. -/
  isTermProof : Bool := false
  /-- Which proof body the tactic family was measured from: `"author"` (source `by`
  block), `"reverse_elab"` (the reverse-elaborated `proof_script`), or `none` (no
  tactic family — either `--proof-metrics` was off, or nothing was measurable).
  A single wide-table row cannot see the run's flags, so this makes each row
  self-describing. See `Corpus.ProofMetrics.sourceAuthor` / `sourceReverseElab`. -/
  tacticMetricsSource : Option String := none
  /-- Top-level author tactic steps. Tactic family: `none` for a term proof, a
  non-theorem, or when `--proof-metrics` is off. -/
  tacticStepCount : Option Nat := none
  /-- Every author tactic, nested children included. `none` as `tacticStepCount`. -/
  tacticTotalCount : Option Nat := none
  /-- Deepest author-tactic nesting (0 for a flat proof). `none` as above. -/
  maxTacticDepth : Option Nat := none
  /-- Sorted distinct tactic-kind strings in the proof. `[]` when not applicable. -/
  tacticKinds : List String := []
  /-- Tactic-kind string → occurrence count. `{}` when not applicable. -/
  tacticHistogram : List (String × Nat) := []
  /-- Case-analysis tactics (`induction`/`cases`/`rcases`/…). `none` as above. -/
  caseSplitCount : Option Nat := none
  /-- Directed rewrites (`rw`/`rewrite`; `simp` counts as automation). `none`. -/
  rewriteCount : Option Nat := none
  /-- Intermediate assertions (`have`/`suffices`/`let`). `none` as above. -/
  haveCount : Option Nat := none
  /-- Steps inside `calc` blocks. `none` as above. -/
  calcSteps : Option Nat := none
  /-- Sorted short names of automation tactics used (`simp`/`omega`/`grind`/…).
  `[]` for a term proof, a manual proof with no automation, or flag off. -/
  automationTactics : List String := []
  /-- Semantic family: distinct sub-expressions of the elaborated proof term.
  Populated for theorems (incl. term-mode) under `--proof-metrics`; `none` for
  non-theorems or when the flag is off. -/
  proofTermSize : Option Nat := none
  /-- Semantic family: approximate depth of the elaborated proof term. `none` as
  `proofTermSize`. -/
  proofTermDepth : Option Nat := none
  /-- Declaration attributes (`@[simp]` → `"simp"`), sorted. Present for term and
  tactic proofs alike under `--proof-metrics`; `[]` when the flag is off or the
  declaration has no attributes. -/
  attributes : List String := []
  /-- Single-declaration mode (`--decl`) only: this record's role in ONE target's
  dependency closure — `"target"`, `"statement"` (reachable from the target's
  type, so needed to state it), or `"proof"` (reachable only through the target's
  proof/value). `none` in every other extraction mode.

  This is a property of the record WITHIN a closure, not of the constant: the same
  lemma is `statement` for one target and `proof` for another, so each target's
  output directory carries its own annotated copy. -/
  closureRole : Option String := none
  deriving Inhabited

namespace ConstRecord

/-- Manual JSON encoder. We don't derive `ToJson` because:
  * Field keys need to be snake_case (HF convention) — derived `ToJson`
    emits the Lean field name verbatim (`sourceText`, `isPrivate`, …)
    and core Lean has no rename attribute.
  * `tags : List (String × String)` should render as a flat
    string→string object (`{"workstream":"B"}`), not the derived
    list-of-pairs form (`[["workstream","B"]]`).

The on-wire field order is alphabetical regardless of how we list keys
here — `Lean.Json.mkObj` is backed by an `RBNode String _`, which sorts
by key. That's deterministic across runs; this list just controls which
keys we emit and what they map to. -/
def toJson (r : ConstRecord) : Json :=
  let tagsJson : Json :=
    Json.mkObj (r.tags.map (fun (k, v) => (k, Json.str v)))
  -- Histogram renders as a flat kind→count object (like `tags`), not a
  -- list-of-pairs, so a consumer reads `{"…rwSeq": 2}` directly.
  let histJson : Json :=
    Json.mkObj (r.tacticHistogram.map (fun (k, n) =>
      (k, Json.num (Lean.JsonNumber.fromNat n))))
  Json.mkObj [
    ("name",         Json.str r.name),
    ("kind",         Json.str r.kind),
    ("module",       Json.str r.module),
    ("file",         Lean.toJson r.file),
    ("start_line",   Lean.toJson r.startLine),
    ("start_col",    Lean.toJson r.startCol),
    ("end_line",     Lean.toJson r.endLine),
    ("end_col",      Lean.toJson r.endCol),
    ("signature",     Lean.toJson r.signature),
    ("body",          Lean.toJson r.body),
    ("decl_source",   Lean.toJson r.declSource),
    ("decl_namespace", Json.str r.declNamespace),
    ("scope_prelude", Lean.toJson r.scopePrelude),
    ("file_imports",  Lean.toJson r.fileImports),
    ("type",          Json.str r.type),
    ("value",        Lean.toJson r.value),
    ("proof_script", Lean.toJson r.proofScript),
    ("proof_method", Lean.toJson r.proofMethod),
    ("doc",          Lean.toJson r.doc),
    ("deps",         Lean.toJson r.deps),
    ("premises",     Lean.toJson r.premises),
    ("axioms",       Lean.toJson r.axioms),
    ("is_protected", Json.bool r.isProtected),
    ("is_private",   Json.bool r.isPrivate),
    ("tags",         tagsJson),
    ("is_term_proof",      Json.bool r.isTermProof),
    ("tactic_metrics_source", Lean.toJson r.tacticMetricsSource),
    ("tactic_step_count",  Lean.toJson r.tacticStepCount),
    ("tactic_total_count", Lean.toJson r.tacticTotalCount),
    ("max_tactic_depth",   Lean.toJson r.maxTacticDepth),
    ("tactic_kinds",       Lean.toJson r.tacticKinds),
    ("tactic_histogram",   histJson),
    ("case_split_count",   Lean.toJson r.caseSplitCount),
    ("rewrite_count",      Lean.toJson r.rewriteCount),
    ("have_count",         Lean.toJson r.haveCount),
    ("calc_steps",         Lean.toJson r.calcSteps),
    ("automation_tactics", Lean.toJson r.automationTactics),
    ("proof_term_size",    Lean.toJson r.proofTermSize),
    ("proof_term_depth",   Lean.toJson r.proofTermDepth),
    ("attributes",         Lean.toJson r.attributes),
    ("closure_role", Lean.toJson r.closureRole)
  ]

instance : ToJson ConstRecord := ⟨toJson⟩

/-- Best-effort decoder, primarily for round-trip tests. The `tags` field is
parsed as a JSON object (string→string), not the derived list-of-pairs form.
Reads the same snake_case keys produced by `toJson`. -/
def fromJson? (j : Json) : Except String ConstRecord := do
  let getStr (k : String) : Except String String := do
    let v ← j.getObjVal? k
    v.getStr?
  let getOptStr (k : String) : Except String (Option String) := do
    match j.getObjVal? k with
    | .ok v => match v with
      | .null => .ok none
      | _     => v.getStr?.map some
    | .error _ => .ok none
  let getOptNat (k : String) : Except String (Option Nat) := do
    match j.getObjVal? k with
    | .ok v => match v with
      | .null => .ok none
      | _     => (Lean.fromJson? v : Except String Nat).map some
    | .error _ => .ok none
  let getBool (k : String) : Except String Bool := do
    let v ← j.getObjVal? k
    v.getBool?
  let getStrList (k : String) : Except String (List String) := do
    let v ← j.getObjVal? k
    let arr ← v.getArr?
    arr.toList.mapM (fun x => x.getStr?)
  -- Accept records produced before `premises` was added.
  let getOptStrList (k : String) : Except String (List String) := do
    match j.getObjVal? k with
    | .ok v =>
        match v.getArr? with
        | .ok arr => arr.toList.mapM (fun x => x.getStr?)
        | .error _ => .ok []
    | .error _ => .ok []
  let tags ← (do
    match j.getObjVal? "tags" with
    | .ok (Json.obj kvs) =>
        let acc := kvs.foldl (init := ([] : List (String × String))) fun acc k v =>
          match v with
          | Json.str s => acc ++ [(k, s)]
          | _          => acc
        .ok acc
    | _ => .ok ([] : List (String × String)))
  -- Proof-metric fields. All tolerate absence (records written before
  -- `--proof-metrics`, or with the flag off) by defaulting to the empty form.
  let getBoolD (k : String) : Except String Bool :=
    match j.getObjVal? k with
    | .ok v    => v.getBool?
    | .error _ => .ok false
  let getOptNat' (k : String) : Except String (Option Nat) :=
    match j.getObjVal? k with
    | .ok .null => .ok none
    | .ok v     => (Lean.fromJson? v : Except String Nat).map some
    | .error _  => .ok none
  let tacticHistogram ← (do
    match j.getObjVal? "tactic_histogram" with
    | .ok (Json.obj kvs) =>
        let acc := kvs.foldl (init := ([] : List (String × Nat))) fun acc k v =>
          match (Lean.fromJson? v : Except String Nat) with
          | .ok n => acc ++ [(k, n)]
          | _     => acc
        .ok acc
    | _ => .ok ([] : List (String × Nat)))
  return {
    name        := ← getStr "name"
    kind        := ← getStr "kind"
    module      := ← getStr "module"
    file        := ← getOptStr "file"
    startLine   := ← getOptNat "start_line"
    startCol    := ← getOptNat "start_col"
    endLine     := ← getOptNat "end_line"
    endCol      := ← getOptNat "end_col"
    signature   := ← getOptStr "signature"
    body        := ← getOptStr "body"
    declSource  := ← getOptStr "decl_source"
    declNamespace := (← getOptStr "decl_namespace").getD ""
    scopePrelude  := ← getOptStrList "scope_prelude"
    fileImports   := ← getOptStrList "file_imports"
    type        := ← getStr "type"
    value       := ← getOptStr "value"
    proofScript := ← getOptStr "proof_script"
    proofMethod := ← getOptStr "proof_method"
    doc         := ← getOptStr "doc"
    deps        := ← getStrList "deps"
    premises    := ← getOptStrList "premises"
    axioms      := ← getStrList "axioms"
    isProtected := ← getBool "is_protected"
    isPrivate   := ← getBool "is_private"
    tags        := tags
    isTermProof       := ← getBoolD "is_term_proof"
    tacticMetricsSource := ← getOptStr "tactic_metrics_source"
    tacticStepCount   := ← getOptNat' "tactic_step_count"
    tacticTotalCount  := ← getOptNat' "tactic_total_count"
    maxTacticDepth    := ← getOptNat' "max_tactic_depth"
    tacticKinds       := ← getOptStrList "tactic_kinds"
    tacticHistogram   := tacticHistogram
    caseSplitCount    := ← getOptNat' "case_split_count"
    rewriteCount      := ← getOptNat' "rewrite_count"
    haveCount         := ← getOptNat' "have_count"
    calcSteps         := ← getOptNat' "calc_steps"
    automationTactics := ← getOptStrList "automation_tactics"
    proofTermSize     := ← getOptNat' "proof_term_size"
    proofTermDepth    := ← getOptNat' "proof_term_depth"
    attributes        := ← getOptStrList "attributes"
    closureRole := ← getOptStr "closure_role"
  }

instance : FromJson ConstRecord := ⟨fromJson?⟩

end ConstRecord

/-! ## Grind manifest records (AlphaGrind data)

A `GrindGoalRecord` is one theorem re-proved by `grind`'s default strategy,
capturing what grind did: the interactive `grind => <seq>` script and the
`grind only [...]` reconstruction (both replayable artifacts), plus the
AlphaGo-style triple — the E-matching lemmas grind's search *activated* (with
counts) and those actually *used* in the final proof term. The env-level
"available" hint set (every `@[grind]` theorem in scope) is written once to
`metadata.json`, not per record. Emitted to `data/grind/*.jsonl`, a config
separate from `theorems`/`definitions` so the corpus schema is unperturbed. -/

structure GrindGoalRecord where
  /-- Fully-qualified theorem name (joins to the `theorems` config by `name`). -/
  name        : String
  /-- The module that elaborated the theorem. -/
  module      : String
  /-- Source path relative to `--source-root`, from discovery. -/
  file        : Option String
  /-- 1-based start line of the theorem's source range. -/
  startLine   : Option Nat
  /-- Pretty-printed goal grind was run on. -/
  goalType    : String
  /-- `closed` / `stuck` / `error` / `deadline_skipped`. -/
  outcome     : String
  /-- Interactive `grind => <seq>` script (primary label); null unless closed. -/
  interactive : Option String
  /-- `grind only [...]` reconstruction (secondary label); null unless closed. -/
  grindOnly   : Option String
  /-- `true` iff grind's generated seq contained `sorry` (artifacts suppressed). -/
  hasSorry    : Bool
  /-- Theorems grind ACTIVATED, `"<name>:<count>"` (local origins prefixed). -/
  activated   : List String
  /-- Global-lemma names that appear in the final proof term (the winning line). -/
  used        : List String
  /-- Count of used origins that were NOT global decls (non-portable reliance). -/
  coverageGap : Nat
  /-- `true` iff the theorem is `private`. -/
  isPrivate   : Bool
  /-- `true` iff the theorem's SOURCE proof already used `grind` (mined seed). -/
  sourceUsesGrind : Bool
  deriving Inhabited

namespace GrindGoalRecord

/-- Manual JSON encoder, snake_case keys (mirrors `ConstRecord.toJson`). -/
def toJson (r : GrindGoalRecord) : Json :=
  Json.mkObj [
    ("name",              Json.str r.name),
    ("module",            Json.str r.module),
    ("file",              Lean.toJson r.file),
    ("start_line",        Lean.toJson r.startLine),
    ("goal_type",         Json.str r.goalType),
    ("outcome",           Json.str r.outcome),
    ("interactive",       Lean.toJson r.interactive),
    ("grind_only",        Lean.toJson r.grindOnly),
    ("has_sorry",         Json.bool r.hasSorry),
    ("activated",         Lean.toJson r.activated),
    ("used",              Lean.toJson r.used),
    ("coverage_gap",      Json.num (Lean.JsonNumber.fromNat r.coverageGap)),
    ("is_private",        Json.bool r.isPrivate),
    ("source_uses_grind", Json.bool r.sourceUsesGrind)
  ]

instance : ToJson GrindGoalRecord := ⟨toJson⟩

end GrindGoalRecord

/-! ## In-proof grind records (AlphaGrind data, observation mode)

A `GrindInProofRecord` is one grind CALL SITE inside an existing proof — a
verification condition on which the source author invoked `grind` (e.g.
`all_goals mleave <;> grind`, `grind [lemmas]`). Unlike `GrindGoalRecord` (which
re-proves whole statements), this captures grind where it actually runs: the
restored subgoal, the author's hint set, and — from re-running instrumented grind
with those hints — the same triple + interactive/`grind only` artifacts. One
theorem yields MANY of these rows (one per grind call site). Emitted to
`data/grind-in-proof/*.jsonl`, a config separate from the whole-statement grind
data so both schemas stay stable. -/

structure GrindInProofRecord where
  /-- Fully-qualified enclosing theorem/def name (one theorem → many VC rows). -/
  enclosingTheorem : String
  /-- The module that elaborated the enclosing declaration. -/
  module      : String
  /-- Source path relative to `--source-root`, from discovery. -/
  file        : Option String
  /-- 1-based source line of the `grind` call. -/
  startLine   : Option Nat
  /-- 0-based source column of the `grind` call. -/
  startCol    : Option Nat
  /-- Pretty-printed restored VC grind was re-run on. -/
  goalType    : String
  /-- The author's hint clause rendered as written, e.g. `"[List.nodup_cons]"`;
  `null` if the source `grind` had no `[..]` clause. -/
  authorHints : Option String
  /-- `true` iff the source call was `grind only …`. -/
  authorOnly  : Bool
  /-- `closed` / `stuck` / `error` / `deadline_skipped`. -/
  outcome     : String
  /-- Interactive `grind => <seq>` script (primary label); null unless closed. -/
  interactive : Option String
  /-- `grind only [...]` reconstruction (secondary label); null unless closed. -/
  grindOnly   : Option String
  /-- `true` iff grind's generated seq contained `sorry` (artifacts suppressed). -/
  hasSorry    : Bool
  /-- Origins grind ACTIVATED, `"<name>:<count>"` (local origins prefixed). -/
  activated   : List String
  /-- Global-lemma names that appear in the final proof term (the winning line). -/
  used        : List String
  /-- Count of used origins that were NOT global decls (non-portable reliance). -/
  coverageGap : Nat
  /-- `true` iff the enclosing declaration is `private`. -/
  isPrivate   : Bool
  deriving Inhabited

namespace GrindInProofRecord

/-- Manual JSON encoder, snake_case keys (mirrors `GrindGoalRecord.toJson`). -/
def toJson (r : GrindInProofRecord) : Json :=
  Json.mkObj [
    ("enclosing_theorem", Json.str r.enclosingTheorem),
    ("module",            Json.str r.module),
    ("file",              Lean.toJson r.file),
    ("start_line",        Lean.toJson r.startLine),
    ("start_col",         Lean.toJson r.startCol),
    ("goal_type",         Json.str r.goalType),
    ("author_hints",      Lean.toJson r.authorHints),
    ("author_only",       Json.bool r.authorOnly),
    ("outcome",           Json.str r.outcome),
    ("interactive",       Lean.toJson r.interactive),
    ("grind_only",        Lean.toJson r.grindOnly),
    ("has_sorry",         Json.bool r.hasSorry),
    ("activated",         Lean.toJson r.activated),
    ("used",              Lean.toJson r.used),
    ("coverage_gap",      Json.num (Lean.JsonNumber.fromNat r.coverageGap)),
    ("is_private",        Json.bool r.isPrivate)
  ]

instance : ToJson GrindInProofRecord := ⟨toJson⟩

end GrindInProofRecord

/-! ## Proof-state records (per-step tactic trajectories)

A `ProofStateRecord` is ONE tactic-proved theorem's full trajectory: the nested
tree of author-written tactics, each step carrying the goal states before and
after it ran. This is the proof's INTERIOR — the thing neither `body` (a source
slice) nor `proof_script` (a reverse-elaborated whole-proof string) can express.

Emitted to `data/proof-states/train.jsonl`, a config separate from
`theorems`/`definitions` so the corpus schema is unperturbed. Joins to the
`theorems` config by `name`.

Three nested types. Goals are INTERNED in a per-record table (`goals`) and
referenced by index, because in a linear proof step `k`'s `goals_after` is step
`k+1`'s `goals_before` — inlining them would nearly double the file and hide that
identity. -/

/-- One hypothesis in a goal's local context. Consecutive same-type declarations
are grouped into one entry (`names`), the way `Meta.ppGoal` renders `a b : Nat`. -/
structure ProofHyp where
  /-- User-facing names sharing this type, in source order. -/
  names : Array String
  /-- Pretty-printed type. -/
  type  : String
  /-- Pretty-printed value, for `let`-bound (`ldecl`) hypotheses only. -/
  value : Option String
  /-- `true` iff this is a `let`-binding rather than a plain hypothesis. -/
  isLet : Bool
  deriving Inhabited, BEq

namespace ProofHyp

def toJson (h : ProofHyp) : Json :=
  Json.mkObj [
    ("names",  Json.arr (h.names.map Json.str)),
    ("type",   Json.str h.type),
    ("value",  Lean.toJson h.value),
    ("is_let", Json.bool h.isLet)
  ]

instance : ToJson ProofHyp := ⟨toJson⟩

def fromJson? (j : Json) : Except String ProofHyp := do
  let names ← do
    let v ← j.getObjVal? "names"
    let arr ← v.getArr?
    arr.mapM (·.getStr?)
  let type ← (← j.getObjVal? "type").getStr?
  let value ← match j.getObjVal? "value" with
    | .ok .null => pure none
    | .ok v     => some <$> v.getStr?
    | .error _  => pure none
  let isLet ← match j.getObjVal? "is_let" with
    | .ok v    => v.getBool?
    | .error _ => pure false
  return { names, type, value, isLet }

instance : FromJson ProofHyp := ⟨fromJson?⟩

end ProofHyp

/-- One goal state: a metavariable's local context and target, rendered.

`pretty` is SYNTHESIZED from `hyps`/`target` rather than obtained by a second
`Meta.ppGoal` call, so the two can never disagree. It is therefore
infoview-*shaped* (`h : T` lines then `⊢ target`) rather than byte-identical to
the infoview. -/
structure ProofGoal where
  /-- Position in the record's `goals` table; steps reference goals by this. -/
  id     : Nat
  /-- The goal metavariable's name, e.g. `"_uniq.412"`. Diagnostic only: the same
  metavariable renders differently under different `MetavarContext` snapshots, so
  this is NOT an identity key (interning is by rendered content). -/
  mvar   : String
  /-- The goal's local context, aux and implementation-detail decls excluded. -/
  hyps   : Array ProofHyp
  /-- Pretty-printed target type. -/
  target : String
  /-- The whole goal as one block: hypothesis lines then `⊢ target`. -/
  pretty : String
  deriving Inhabited, BEq

namespace ProofGoal

def toJson (g : ProofGoal) : Json :=
  Json.mkObj [
    ("id",     Json.num (JsonNumber.fromNat g.id)),
    ("mvar",   Json.str g.mvar),
    ("hyps",   Json.arr (g.hyps.map ProofHyp.toJson)),
    ("target", Json.str g.target),
    ("pretty", Json.str g.pretty)
  ]

instance : ToJson ProofGoal := ⟨toJson⟩

def fromJson? (j : Json) : Except String ProofGoal := do
  let id ← (Lean.fromJson? (← j.getObjVal? "id") : Except String Nat)
  let mvar ← (← j.getObjVal? "mvar").getStr?
  let hyps ← do
    let v ← j.getObjVal? "hyps"
    let arr ← v.getArr?
    arr.mapM ProofHyp.fromJson?
  let target ← (← j.getObjVal? "target").getStr?
  let pretty ← (← j.getObjVal? "pretty").getStr?
  return { id, mvar, hyps, target, pretty }

instance : FromJson ProofGoal := ⟨fromJson?⟩

end ProofGoal

/-- One author-written tactic and its effect on the goal state.

`children` carries the tactics a combinator composed: `induction … with` holds its
per-alternative tactics, `t <;> u` holds `t` and `u`, `·` holds its focused block.
That nesting mirrors the source structure.

Byte offsets are file-relative and make a step locatable inside the existing
corpus schema without re-elaborating:
`start_byte - ProofStateRecord.proofStartByte` is the step's offset within that
theorem's `ConstRecord.body`. -/
structure ProofStep where
  /-- Pre-order index, dense within one record. -/
  index       : Nat
  /-- Nesting depth; top-level tactics are 0. -/
  depth       : Nat
  /-- VERBATIM source text of the tactic, sliced from the file — never
  pretty-printed or `reprint`ed, so it is exactly what the author wrote. For a
  combinator this spans the whole construct, children included. -/
  tactic      : String
  /-- Syntax node kind, e.g. `"Lean.Parser.Tactic.induction"`. Always a member of
  the `tactic` or `conv` parser category. -/
  tacticKind  : String
  /-- The elaborator that ran it (`TacticInfo.elaborator`). -/
  elaborator  : String
  startLine   : Nat
  startCol    : Nat
  endLine     : Nat
  endCol      : Nat
  /-- File-relative byte offset of the tactic's first character. -/
  startByte   : Nat
  /-- File-relative byte offset one past the tactic's last character. -/
  endByte     : Nat
  /-- Indices into the record's `goals` table: the goals this tactic ran on. -/
  goalsBefore : Array Nat
  /-- Indices into `goals`: the goals remaining after it ran. Empty means the
  tactic closed everything it was given. -/
  goalsAfter  : Array Nat
  /-- How many times this syntax was invoked. `> 1` means a combinator
  (`all_goals`, `<;>`, `repeat`) re-ran it once per goal, and `goals_before` /
  `goals_after` are the unions across those invocations. -/
  invocations : Nat
  /-- Tactics this one composed, in source order. -/
  children    : Array ProofStep
  deriving Inhabited

namespace ProofStep

/-- Manual JSON encoder, snake_case keys. `partial` because `ProofStep` is
recursive through `children`. -/
partial def toJson (s : ProofStep) : Json :=
  Json.mkObj [
    ("index",        Json.num (JsonNumber.fromNat s.index)),
    ("depth",        Json.num (JsonNumber.fromNat s.depth)),
    ("tactic",       Json.str s.tactic),
    ("tactic_kind",  Json.str s.tacticKind),
    ("elaborator",   Json.str s.elaborator),
    ("start_line",   Json.num (JsonNumber.fromNat s.startLine)),
    ("start_col",    Json.num (JsonNumber.fromNat s.startCol)),
    ("end_line",     Json.num (JsonNumber.fromNat s.endLine)),
    ("end_col",      Json.num (JsonNumber.fromNat s.endCol)),
    ("start_byte",   Json.num (JsonNumber.fromNat s.startByte)),
    ("end_byte",     Json.num (JsonNumber.fromNat s.endByte)),
    ("goals_before", Json.arr (s.goalsBefore.map (Json.num ∘ JsonNumber.fromNat))),
    ("goals_after",  Json.arr (s.goalsAfter.map (Json.num ∘ JsonNumber.fromNat))),
    ("invocations",  Json.num (JsonNumber.fromNat s.invocations)),
    ("children",     Json.arr (s.children.map toJson))
  ]

instance : ToJson ProofStep := ⟨toJson⟩

private def getNat (j : Json) (k : String) : Except String Nat := do
  (Lean.fromJson? (← j.getObjVal? k) : Except String Nat)

private def getNatArr (j : Json) (k : String) : Except String (Array Nat) := do
  let v ← j.getObjVal? k
  let arr ← v.getArr?
  arr.mapM fun x => (Lean.fromJson? x : Except String Nat)

partial def fromJson? (j : Json) : Except String ProofStep := do
  let children ← do
    match j.getObjVal? "children" with
    | .ok v    => (← v.getArr?).mapM fromJson?
    | .error _ => pure #[]
  return {
    index       := ← getNat j "index"
    depth       := ← getNat j "depth"
    tactic      := ← (← j.getObjVal? "tactic").getStr?
    tacticKind  := ← (← j.getObjVal? "tactic_kind").getStr?
    elaborator  := ← (← j.getObjVal? "elaborator").getStr?
    startLine   := ← getNat j "start_line"
    startCol    := ← getNat j "start_col"
    endLine     := ← getNat j "end_line"
    endCol      := ← getNat j "end_col"
    startByte   := ← getNat j "start_byte"
    endByte     := ← getNat j "end_byte"
    goalsBefore := ← getNatArr j "goals_before"
    goalsAfter  := ← getNatArr j "goals_after"
    invocations := ← getNat j "invocations"
    children    := children
  }

instance : FromJson ProofStep := ⟨fromJson?⟩

end ProofStep

/-- One tactic-proved theorem's trajectory. Theorems proved by a bare term
(`:= rfl`, no `by`) produce no tactic nodes and are NOT emitted — they are counted
as skipped instead, so a consumer never sees a row with an empty `steps`. -/
structure ProofStateRecord where
  /-- Fully-qualified theorem name; joins to the `theorems` config. -/
  name           : String
  /-- The module that elaborated it. -/
  module         : String
  /-- Source path relative to `--source-root`, from discovery. -/
  file           : Option String
  /-- 1-based start line of the declaration's full source range. -/
  startLine      : Option Nat
  /-- 0-based start column. -/
  startCol       : Option Nat
  /-- 1-based end line. -/
  endLine        : Option Nat
  /-- 0-based end column. -/
  endCol         : Option Nat
  /-- `"theorem"` or `"private theorem"`, matching the corpus `kind`. -/
  declKind       : String
  /-- File-relative byte offset of the proof value (the `by …` term). -/
  proofStartByte : Nat
  /-- File-relative byte offset one past the proof value. -/
  proofEndByte   : Nat
  /-- VERBATIM proof source, `by` included — the same bytes as the corpus
  record's `body`, restated here so this dataset stands alone. -/
  proofSource    : String
  /-- For a `where` / `let rec` AUXILIARY, the enclosing declaration's source name;
  `none` for a top-level theorem.

  An auxiliary is lifted by Lean into its own separately-checked constant and gets
  its own record, because it is frequently the substantive lemma (the parent's proof
  being a one-line `exact aux …`). This field is what lets a consumer group a proof
  with its auxiliaries, or filter them out.

  Derived from the SOURCE syntax, not by splitting the constant's name: an auxiliary
  is named `<parent>.<aux>`, but so is any namespaced theorem, so name-splitting
  would misclassify ordinary declarations as auxiliaries. -/
  parentDecl     : Option String
  /-- The interned goal table. `ProofGoal.id` equals the index. -/
  goals          : Array ProofGoal
  /-- Indices into `goals`: the goal state the proof opened with. -/
  initialGoals   : Array Nat
  /-- The tactic tree, top-level tactics in source order. -/
  steps          : Array ProofStep
  /-- Total steps including nested children. -/
  stepCount      : Nat
  /-- Deepest nesting level reached (0 for a flat proof). -/
  maxDepth       : Nat
  /-- Sorted distinct `tactic_kind`s in the proof, for cheap filtering. -/
  tacticKinds    : Array String
  /-- `true` iff the theorem's transitive axioms include `sorryAx`. -/
  hasSorry       : Bool
  /-- `"ok"` / `"skipped_large"` / `"deadline_skipped"` / `"error"`. Anything but
  `"ok"` means `steps` is empty and the trajectory was not captured. -/
  outcome        : String
  /-- `true` iff the theorem is `private`. -/
  isPrivate      : Bool
  deriving Inhabited

namespace ProofStateRecord

/-- Manual JSON encoder, snake_case keys (mirrors `GrindInProofRecord.toJson`). -/
def toJson (r : ProofStateRecord) : Json :=
  Json.mkObj [
    ("name",             Json.str r.name),
    ("module",           Json.str r.module),
    ("file",             Lean.toJson r.file),
    ("start_line",       Lean.toJson r.startLine),
    ("start_col",        Lean.toJson r.startCol),
    ("end_line",         Lean.toJson r.endLine),
    ("end_col",          Lean.toJson r.endCol),
    ("decl_kind",        Json.str r.declKind),
    ("proof_start_byte", Json.num (JsonNumber.fromNat r.proofStartByte)),
    ("proof_end_byte",   Json.num (JsonNumber.fromNat r.proofEndByte)),
    ("proof_source",     Json.str r.proofSource),
    ("parent_decl",      Lean.toJson r.parentDecl),
    ("goals",            Json.arr (r.goals.map ProofGoal.toJson)),
    ("initial_goals",    Json.arr (r.initialGoals.map (Json.num ∘ JsonNumber.fromNat))),
    ("steps",            Json.arr (r.steps.map ProofStep.toJson)),
    ("step_count",       Json.num (JsonNumber.fromNat r.stepCount)),
    ("max_depth",        Json.num (JsonNumber.fromNat r.maxDepth)),
    ("tactic_kinds",     Json.arr (r.tacticKinds.map Json.str)),
    ("has_sorry",        Json.bool r.hasSorry),
    ("outcome",          Json.str r.outcome),
    ("is_private",       Json.bool r.isPrivate)
  ]

instance : ToJson ProofStateRecord := ⟨toJson⟩

/-- Decoder, primarily for round-trip tests and golden-fixture checks. -/
def fromJson? (j : Json) : Except String ProofStateRecord := do
  let getOptNat (k : String) : Except String (Option Nat) :=
    match j.getObjVal? k with
    | .ok .null => .ok none
    | .ok v     => (Lean.fromJson? v : Except String Nat).map some
    | .error _  => .ok none
  let getNat (k : String) : Except String Nat := do
    (Lean.fromJson? (← j.getObjVal? k) : Except String Nat)
  let getNatArr (k : String) : Except String (Array Nat) := do
    let v ← j.getObjVal? k
    (← v.getArr?).mapM fun x => (Lean.fromJson? x : Except String Nat)
  return {
    name           := ← (← j.getObjVal? "name").getStr?
    module         := ← (← j.getObjVal? "module").getStr?
    file           := ← (match j.getObjVal? "file" with
                          | .ok .null => .ok none
                          | .ok v     => v.getStr?.map some
                          | .error _  => .ok none)
    startLine      := ← getOptNat "start_line"
    startCol       := ← getOptNat "start_col"
    endLine        := ← getOptNat "end_line"
    endCol         := ← getOptNat "end_col"
    declKind       := ← (← j.getObjVal? "decl_kind").getStr?
    proofStartByte := ← getNat "proof_start_byte"
    proofEndByte   := ← getNat "proof_end_byte"
    proofSource    := ← (← j.getObjVal? "proof_source").getStr?
    parentDecl     := ← (match j.getObjVal? "parent_decl" with
                          | .ok .null => .ok none
                          | .ok v     => v.getStr?.map some
                          | .error _  => .ok none)
    goals          := ← (do let v ← j.getObjVal? "goals"
                            (← v.getArr?).mapM ProofGoal.fromJson?)
    initialGoals   := ← getNatArr "initial_goals"
    steps          := ← (do let v ← j.getObjVal? "steps"
                            (← v.getArr?).mapM ProofStep.fromJson?)
    stepCount      := ← getNat "step_count"
    maxDepth       := ← getNat "max_depth"
    tacticKinds    := ← (do let v ← j.getObjVal? "tactic_kinds"
                            (← v.getArr?).mapM (·.getStr?))
    hasSorry       := ← (← j.getObjVal? "has_sorry").getBool?
    outcome        := ← (← j.getObjVal? "outcome").getStr?
    isPrivate      := ← (← j.getObjVal? "is_private").getBool?
  }

instance : FromJson ProofStateRecord := ⟨fromJson?⟩

end ProofStateRecord

end Corpus
