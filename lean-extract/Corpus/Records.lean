import Lean
import WorkerPlugins.ReverseElab

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
  proofTrace  : Option (Array WorkerPlugins.ReverseElab.TraceEntry) := none
  proofStructTree : Option (Array WorkerPlugins.ReverseElab.StructNode) := none
  doc         : Option String
  deps        : List String
  premises    : List String
  axioms      : List String
  isProtected : Bool
  isPrivate   : Bool
  tags        : List (String × String)
  deriving Inhabited

namespace ConstRecord

/-- Summarize a `proof_trace` into `{last_status, attempts}`: a STABLE categorical
label for the terminal state of reverse-elaboration and how many ladder rungs were
actually tried. `last_status` is one of `success`, `verify_failed` (all rungs tried,
none verified), `skipped_large` (pre-filtered), `file_timeout`, `runtime_error`, or
`none` — deliberately free of embedded numbers (node counts) so consumers can bucket
by it directly; the detail stays in `proof_trace`. A `pre_filter`/`file_timeout`/
`runtime` entry counts as 0 real attempts (no rung ran); every other entry is one. -/
private def summarizeTrace (entries : Array WorkerPlugins.ReverseElab.TraceEntry) : Json :=
  let lastStatus := match entries.back? with
    | none   => "none"
    | some e =>
      if e.result == "success" then "success"
      else if e.rung == "pre_filter" then "skipped_large"
      else if e.rung == "file_timeout" then "file_timeout"
      else if e.rung == "runtime" then "runtime_error"
      else "verify_failed"
  let attempts := entries.foldl (init := 0) fun n e =>
    if e.rung == "pre_filter" || e.rung == "file_timeout" || e.rung == "runtime"
    then n else n + 1
  Json.mkObj [
    ("last_status", Json.str lastStatus),
    ("attempts",    Json.num (JsonNumber.fromNat attempts))
  ]

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
  let base := [
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
  let withTrace := match r.proofTrace with
    | some entries => base ++ [
        ("proof_trace",         Lean.toJson entries),
        ("proof_trace_summary", summarizeTrace entries)]
    | none         => base
  let fields := match r.proofStructTree with
    | some tree => withTrace ++ [("proof_struct_tree", Lean.toJson tree)]
    | none      => withTrace
  Json.mkObj fields

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
    type        := ← getStr "type"
    value       := ← getOptStr "value"
    proofScript := ← getOptStr "proof_script"
    proofMethod := ← getOptStr "proof_method"
    proofTrace  := match j.getObjVal? "proof_trace" with
      | .ok v => match v with
        | .null => none
        | _     => (Lean.fromJson? v).toOption
      | .error _ => none
    proofStructTree := match j.getObjVal? "proof_struct_tree" with
      | .ok v => match v with
        | .null => none
        | _     => (Lean.fromJson? v).toOption
      | .error _ => none
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

end Corpus
