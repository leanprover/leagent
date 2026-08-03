# Spec: `Corpus.Json` — a wire-format layer over Lean's JSON library

## Status

Design spec. Nothing implemented. Every mechanism below was prototyped against
Lean **4.31.0** and confirmed to work or to be impossible; the findings are
recorded inline as **PROVEN** / **BLOCKED** so an implementer does not have to
rediscover them.

## Motivation

`Corpus.Records` hand-writes `ToJson`/`FromJson` for `ConstRecord` (~90 lines for
one 26-field structure), and `Corpus.DeclClosure.Emit` hand-builds
`metadata.json` and `dropped.json` with no backing type at all. That is not
stylistic: derived instances cannot express what the dataset's wire format
requires. But the hand-written versions cost us real defects — a versioned format
(`lean-corpus-dropped.v1`) with no type enforcing it, and a doc/code drift caught
only by grep.

Lean core has the same problem: six files under `Lean/Data/Lsp/` hand-write
instances because LSP's wire keys don't match Lean identifier style. Upstream has
no fix and none planned (searched `leanprover/lean4` issues, Reservoir's 790
packages, and the community cookbook — the cookbook's own guidance is
"manually implement `ToJson` and `FromJson`").

This library closes the gap **for us**, as a thin layer over `Lean.Json` rather
than a replacement. If the design proves out, the naming-policy part is the
natural upstream RFC.

## Non-goals

- **Not** a new JSON AST. We keep `Lean.Json` as the value type, so every existing
  instance, `Json.compress`/`render`, and `json%` interpolation keep working.
- **Not** a parser. `Json.parse` stays.
- **Not** a general schema/validation system. No JSON Schema emission.
- **Not** a replacement for `deriving ToJson`. Where the derived instance is
  already correct (camelCase, no custom shapes), it stays the right answer.

## The four gaps, and what closes each

| # | Gap | Verified status | Closed by |
|---|---|---|---|
| 1 | No key renaming; derived keys are Lean field names verbatim | BLOCKED as attributes, PROVEN via macro | `json_structure` command + `@[json_policy]` |
| 2 | No per-field codec; a field's type dictates its wire shape | PROVEN | `JsonCodec tag α` tagged class |
| 3 | Key order is lost (`Json.obj` is a sorted `TreeMap.Raw`) | PROVEN unavoidable in `Json`; PROVEN fixable at render | `Corpus.Json.renderOrdered` |
| 4 | Derived `FromJson` is all-or-nothing strict | PROVEN | `json_structure` per-field `default:` |

### Gap 1 findings, in detail

**BLOCKED: Go-style field annotations cannot be attributes.** Lean rejects them
outright:

```lean
structure S where
  @[inline] foo : Nat
-- error: Invalid attribute: Attributes cannot be added to fields
```

So the literal Go shape — `Field int \`json:"myName"\`` — is unavailable as an
attribute. Two consequences: the syntax must come from a **command macro** that
owns the whole structure declaration, and `deriving ToJson with <args>` is also
out, because `derivingClass` is a bare `termParser` and handlers dispatch on class
name only (`Lean/Parser/Command.lean:189`, `Lean/Elab/Deriving/Basic.lean:286`).

**PROVEN: a command macro can carry per-field keys.** Prototype emitted
`[("startLine", "start_line"), ("plain", "plain")]` from a declaration that also
produced a working `structure`.

**PROVEN: a structure-level attribute works and survives imports**, so the
common case (a whole-structure naming policy) needs no per-field annotation at
all. Prototype read back `policy for S = (some snake_case)` from a downstream
module via a `SimplePersistentEnvExtension`.

## Design

### 1. Naming policy — the 90% case

Most structures need one rule for every field. That is an attribute on the
structure, which Lean allows:

```lean
@[json_policy snake_case]
structure ConstRecord where
  startLine : Option Nat      -- → "start_line"
  isPrivate : Bool            -- → "is_private"
  deriving Corpus.ToJsonW, Corpus.FromJsonW
```

Policies: `asIs` (default, identical to Lean's behavior), `snakeCase`,
`kebabCase`, `camelCase`, `pascalCase`.

`ToJsonW` / `FromJsonW` ("W" for wire) are new deriving handlers. They reuse
Lean's field enumeration (`getStructureFieldsFlattened`) and its per-field
`toJson`/`fromJson?` dispatch; the only thing they change is the key string and
the per-field codec lookup. **A structure with no policy and no overrides derives
byte-identically to Lean's own `deriving ToJson`** — that equivalence is a test
obligation (see Testing).

### 2. Per-field overrides — the 10% case

When one field disagrees with the policy, or needs a non-default shape, declare
the structure with `json_structure`:

```lean
@[json_policy snake_case]
json_structure ConstRecord where
  startLine : Option Nat
  tags      : List (String × String)  json_codec flatMap
  odataType : String                  json "@odata.type"
  premises  : List String             default []
  deriving Corpus.ToJsonW, Corpus.FromJsonW
```

Per-field clauses, all optional and combinable:

| Clause | Effect |
|---|---|
| `json "<key>"` | Override the wire key, ignoring the policy. |
| `json_codec <tag>` | Encode/decode via `JsonCodec <tag>` instead of the canonical instance. |
| `default <term>` | On decode, use `<term>` when the key is absent or malformed. |
| `omit_if_none` | Omit the key entirely when `none`, rather than emitting `null`. |

`json_structure` expands to an ordinary `structure` plus a registered field-spec
table, so the resulting type is indistinguishable from a hand-written one:
projections, pattern matching, `structure` instance syntax, and other `deriving`
handlers all behave normally. This is the mechanism that recovers the Go
annotation ergonomics under Lean's constraint.

**On `omit_if_none` vs Lean's trailing `?`.** Lean already has an undocumented
convention: a field named `foo?` emits under `"foo"` and is *omitted* when `none`
(`Lean/Elab/Deriving/FromToJson.lean:30`, verified). We deliberately do not adopt
it, for two reasons: it couples the Lean identifier to the wire format (the same
coupling gap 1 exists to break), and omission is the wrong default for our data —
HuggingFace wants the key present with `null` so columns stay stable across
shards. Our default is therefore "emit `null`", with `omit_if_none` as opt-in.

### 3. Custom marshallers

Three levels, in increasing generality.

**Per-field, by tag.** For "this field's type is right for Lean but wrong for the
wire." PROVEN:

```lean
class JsonCodec (tag : Name) (α : Type) where
  enc : α → Json
  dec : Json → Except String α

instance : JsonCodec `flatMap (List (String × String)) where
  enc kvs := Json.mkObj (kvs.map fun (k, v) => (k, Json.str v))
  dec j   := ...
```

Prototype output: `{"workstream":"B"}` with the codec, `[["workstream","B"]]`
without — precisely the `ConstRecord.tags` gap. Tagging (rather than a bare
`ToJson` instance) matters because the same type can need different shapes in
different fields, and because a bare instance on `List (String × String)` would
override that type's encoding program-wide.

**Whole type, by instance.** For "this type always has this wire shape." Write
`ToJsonW`/`FromJsonW` by hand and every field of that type picks it up. This is
the ordinary type-class escape hatch and needs no new machinery.

**Inductives.** Lean's derived encoding for inductives is a tagged object
(`{"ctorName": [args]}`), which is fine for internal data and wrong for most
external formats. `ToJsonW` supports a discriminator style:

```lean
@[json_tagged discriminator := "kind", style := adjacent]
inductive Outcome where
  | closed (script : String)
  | stuck
  | error (message : String)
  deriving Corpus.ToJsonW
```

Styles: `external` (Lean's current `{"closed": …}`), `adjacent`
(`{"kind": "closed", "script": …}`), `internal` (`{"kind": "closed", …}` flattened
where the payload is a structure). `adjacent` is what most REST APIs expect and
what our `DropReason`-style labels would want if they ever became a real type
again.

### 4. Ordered output

`Json.obj` holds a `Std.TreeMap.Raw String Json` (`Lean/Data/Json/Basic.lean:186`),
so key order is *structurally* unrecoverable from a `Json` value — verified:
`Json.mkObj [("zebra",…), ("apple",…)]` renders `{"apple":2,"zebra":1}`.

Consequences worth stating plainly, because this bit us: adding a field to
`ConstRecord` changes **every line's bytes**, since the new key sorts into the
middle rather than appending. Anything diffing or hashing published output sees a
difference.

We do not fork `Json`. Instead `ToJsonW` can additionally emit a
`Corpus.Json.Ordered` — a `List (String × Json)` retaining declaration order —
with `renderOrdered` / `compressOrdered` writers. PROVEN: prototype emitted
`{"zebra":1, "apple":2}` in declaration order. Sorted output stays the default
(it is deterministic and matches existing datasets); ordered emission is opt-in
per writer, for formats where append-only evolution matters.

## API surface

```text
Corpus/Json/Policy.lean    KeyPolicy, @[json_policy], the env extension
Corpus/Json/Codec.lean     JsonCodec class + the codecs we ship (flatMap, …)
Corpus/Json/Spec.lean      json_structure command, field-spec table
Corpus/Json/Derive.lean    ToJsonW / FromJsonW deriving handlers
Corpus/Json/Ordered.lean   Ordered, renderOrdered, compressOrdered
Corpus/Json.lean           re-export
```

Everything lives under `Corpus.Json` and depends only on `Lean`. It is
extractor-agnostic, so it can be split into its own package (or proposed
upstream) without touching call sites.

## Migration

Staged, each stage independently shippable and byte-verifiable.

1. **Land the library with zero call-site changes.** Prove `ToJsonW` ≡ derived
   `ToJson` for policy-free structures, and `snakeCase` ≡ the hand-written
   `ConstRecord.toJson` for the current schema.
2. **`metadata.json` / `dropped.json` first.** These are camelCase, so they need
   no policy — they only need *types*. Lowest risk, and it is where we actually
   lost type checking. Replaces two untyped renderers.
3. **`ConstRecord`** once stage 1's byte-equality test passes, deleting ~90 lines.
   Requires `snakeCase` + `flatMap` codec + `default` for the lenient fields.
4. **Grind records**, mechanically, once `ConstRecord` is proven.
5. **Optional, separate decision:** `reassemble`'s report/manifest JSON.

Byte-for-byte equality against current output is the gate for stages 3–4. Stage 2
changes no existing bytes at all.

## Testing

- **Equivalence:** for a policy-free structure, `ToJsonW` output must equal
  `deriving ToJson` output exactly. This is what keeps the layer honest.
- **Golden schema:** encode a fixed `ConstRecord` and compare against a committed
  fixture, so any accidental key change fails CI. This is the test whose absence
  let the doc drift happen.
- **Round-trip:** `fromJsonW? ∘ toJsonW = id` across policies, codecs, defaults,
  and `omit_if_none`.
- **Backward compatibility:** decode a record captured *before* a field was added
  and require success — the property that let `closure_role` land safely.
- **Policy unit tests:** `startLine → start_line`, `isPrivate → is_private`,
  `odataType` with explicit override, and idempotence (`snakeCase` of an
  already-snake key).
- **Ordering:** `renderOrdered` preserves declaration order; adding a field
  appends rather than reorders.

## Risks

- **Metaprogramming weight.** A command macro plus two deriving handlers is real
  maintenance, and it will break on Lean upgrades that touch
  `getStructureFieldsFlattened` or the deriving API. Mitigation: keep the handlers
  thin — delegate all per-field encoding to existing `ToJson` instances, and own
  only key computation and codec lookup.
- **Two ways to declare a structure.** `structure` + `@[json_policy]` for the
  common case, `json_structure` when a field needs an override. Acceptable only
  if `json_structure` produces an indistinguishable type; that is a test
  obligation, not an assumption.
- **Error quality.** Lean's derived `FromJson` already prefixes failures with
  `Type.field:`. Ours must do at least as well, including for codec and default
  failures, or debugging regresses.
- **`json_structure` and other deriving handlers.** Must confirm `deriving
  Inhabited, BEq, Repr` still work on a `json_structure`-declared type. Untested;
  verify before committing to the syntax.

## Open questions

1. **Policy inheritance.** Should a nested structure inherit its parent's policy,
   or carry its own? Leaning "its own" — a type's wire shape shouldn't depend on
   where it is used — but that means every structure in a tree needs the
   attribute.
2. **Is `json_structure` worth it at all?** If `@[json_policy]` plus whole-type
   `ToJsonW` instances cover our real cases, per-field syntax may be unnecessary
   complexity. Our actual need is narrow: one policy plus `tags`'s shape plus
   leniency on two fields. Worth building stage 1–2 first and re-deciding.
3. **Upstream split.** The naming policy is the generally useful part and the
   plausible RFC. Codecs and `json_structure` are more opinionated. Keep them
   separable in case only the first is proposed.
4. **`Nat` encoding.** Lean emits `Nat` as a JSON number; large values exceed
   double precision. Not a problem for our line/column data, but a general
   library should decide (and document) whether to offer string encoding.
