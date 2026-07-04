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
  Json.mkObj [
    ("name",         Json.str r.name),
    ("kind",         Json.str r.kind),
    ("module",       Json.str r.module),
    ("file",         Lean.toJson r.file),
    ("start_line",   Lean.toJson r.startLine),
    ("start_col",    Lean.toJson r.startCol),
    ("end_line",     Lean.toJson r.endLine),
    ("end_col",      Lean.toJson r.endCol),
    ("signature",    Lean.toJson r.signature),
    ("body",         Lean.toJson r.body),
    ("decl_source",  Lean.toJson r.declSource),
    ("type",         Json.str r.type),
    ("value",        Lean.toJson r.value),
    ("proof_script", Lean.toJson r.proofScript),
    ("proof_method", Lean.toJson r.proofMethod),
    ("doc",          Lean.toJson r.doc),
    ("deps",         Lean.toJson r.deps),
    ("premises",     Lean.toJson r.premises),
    ("axioms",       Lean.toJson r.axioms),
    ("is_protected", Json.bool r.isProtected),
    ("is_private",   Json.bool r.isPrivate),
    ("tags",         tagsJson)
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

end Corpus
