/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean.Server.Requests
import Lean.Server.Snapshots
import Lean.Util.CollectAxioms
import Lean.Data.Lsp.Basic
import WorkerPlugins.Common

/-!
`$/lean/declManifest`: a first-class FileWorker request that returns a per-file fingerprint of
every constant introduced by the file. The response lists, for each module-local constant, its
kind, an alpha-canonical encoding of its elaborated type, the (sorted) set of axioms it
transitively depends on, and a derived `hasSorry` flag.

This is a generic introspection primitive — useful to audit (lean-mcp, lean-verify), Mathlib CI
diff tools, refactor tools, and anything else that wants a stable "what does this file declare"
surface without parsing source. The handler runs after `cmdSnaps.waitAll`, so it always sees the
post-elaboration environment. Internal-detail names (`_aux`, `match_`, equation-compiler shards,
…) are filtered out, since those would otherwise dominate the diff with elaboration-private noise.

This file is built as a Lean **plugin** (a `.so` with an `initialize` block). When the worker
loads the plugin, the `initialize` block at the bottom of this file calls
`registerLspRequestHandler`, which mutates the worker's per-process handler table — from that
point on the worker dispatches `$/lean/declManifest` exactly like any built-in handler.

Use case sketch: a verifier compares a baseline `DeclManifest` (captured before the agent
attempted a proof) against the post-attempt manifest. Differences in `typeRepr` on a target
theorem mean the statement was changed; new axioms or `hasSorry := true` mean the proof is
weaker than asked.
-/

namespace Lean.Lsp

/-- Parameters for `$/lean/declManifest`. -/
structure DeclManifestParams where
  textDocument : TextDocumentIdentifier
  deriving FromJson, ToJson

instance : FileSource DeclManifestParams where
  fileSource p := p.textDocument.uri

/-- One entry in the declaration manifest. -/
structure DeclManifestEntry where
  /-- Fully qualified name. -/
  name        : String
  /-- One of `axiom`, `theorem`, `definition`, `opaque`, `inductive`, `constructor`, `recursor`,
  `quotient`. The audit layer treats `axiom` specially. -/
  kind        : String
  /-- A faithful, alpha-canonical textual encoding of the elaborated type. Two declarations have
  equal `typeRepr` iff their elaborated types are structurally equal modulo binder names,
  level-parameter names, and `mdata` wrappers. Comparing strings on this field is observationally
  equivalent to running `Expr` structural equality on the worker. The encoding is an internal
  format and not intended to be parsed; see `WorkerPlugins.DeclManifest.Expr.canonical`. -/
  typeRepr    : String
  /-- The constant's universe-parameter names, in declaration order. The audit treats a difference
  in *length* as a meaningful change but ignores name renames (those are already absorbed by
  `typeRepr`'s positional encoding of `Level.param`). -/
  levelParams : Array String
  /-- Names of axioms the declaration transitively depends on, sorted lexicographically. -/
  axioms      : Array String
  /-- `true` iff `axioms` contains `sorryAx`. Mirrors what `#print axioms` would say. -/
  hasSorry    : Bool
  deriving FromJson, ToJson

/-- Response payload for `$/lean/declManifest`. -/
structure DeclManifest where
  entries : Array DeclManifestEntry
  deriving FromJson, ToJson

end Lean.Lsp

namespace WorkerPlugins.DeclManifest

open Lean Lean.Lsp Lean.Server Lean.Server.FileWorker Lean.Server.Snapshots

/-! ## Canonical Expr / Level encoding for `typeRepr`

The encoding is a deterministic textual form that visits every `Expr`/`Level` constructor field.
Three properties matter:

1. **Faithful** for elaborated types: two distinct `Expr`s (modulo the equivalence below) produce
   distinct strings. We rely on this because the audit compares strings byte-for-byte.
2. **Alpha-canonical at the term level**: `lam`/`forallE`/`letE` binder names are *omitted* —
   the body uses de Bruijn indices, so renaming the binder is unobservable.
3. **Alpha-canonical at the universe level**: `Level.param n` is emitted positionally as
   `p<i>` where `i` is `n`'s position in the constant's `levelParams`, so renaming a universe
   parameter doesn't change the encoding.

We also drop `mdata` wrappers (purely elaboration-routing hints) and length-prefix `Name`s and
string literals so the encoding is unambiguously parseable in principle (we never parse it; it's
just for equality comparison).

The encoding is an internal format. The baseline lives only in the consumer's memory, so we can
change the encoding any time without a migration. -/

/-- Length-prefixed encoding of a `Name`. We use `<len>:<toString>` so adjacency between names
and other encoded fields is unambiguous. -/
private def encodeName (n : Name) : String :=
  let s := n.toString
  s!"{s.utf8ByteSize}:{s}"

private def encodeBinderInfo : BinderInfo → String
  | .default        => "d"
  | .implicit       => "i"
  | .strictImplicit => "si"
  | .instImplicit   => "ii"

private def encodeLiteral : Literal → String
  | .natVal n => s!"n{n}"
  | .strVal s => s!"s{s.utf8ByteSize}:{s}"

/-- Canonical encoding of a `Level`. `paramIdx` maps each universe-parameter name in the enclosing
constant's `levelParams` to its index, so `Level.param n` is rendered positionally. -/
private partial def Level.canonical (paramIdx : Std.HashMap Name Nat) : Level → String
  | .zero      => "0"
  | .succ l    => s!"s({Level.canonical paramIdx l})"
  | .max a b   => s!"M({Level.canonical paramIdx a},{Level.canonical paramIdx b})"
  | .imax a b  => s!"I({Level.canonical paramIdx a},{Level.canonical paramIdx b})"
  | .param n   =>
    match paramIdx[n]? with
    | some i => s!"p{i}"
    | none   => s!"p?{encodeName n}"  -- shouldn't happen for elaborated `ConstantInfo.type`
  | .mvar id   => s!"mv{encodeName id.name}"

/-- Canonical encoding of an `Expr`. See the section comment above. -/
private partial def Expr.canonical (paramIdx : Std.HashMap Name Nat) (e : Expr) : String :=
  let lvl := Level.canonical paramIdx
  let rec go (e : Expr) : String :=
    match e with
    | .bvar i              => s!"#{i}"
    | .fvar id             => s!"f{encodeName id.name}"          -- shouldn't appear post-elab
    | .mvar id             => s!"m{encodeName id.name}"          -- shouldn't appear post-elab
    | .sort u              => s!"S({lvl u})"
    | .const n us          =>
      let ls := String.intercalate "," (us.map lvl)
      s!"C({encodeName n};{ls})"
    | .app f a             => s!"A({go f},{go a})"
    | .lam _ t b bi        => s!"L({encodeBinderInfo bi},{go t},{go b})"
    | .forallE _ t b bi    => s!"P({encodeBinderInfo bi},{go t},{go b})"
    | .letE _ t v b nondep => s!"Le({if nondep then "1" else "0"},{go t},{go v},{go b})"
    | .lit l               => s!"K({encodeLiteral l})"
    | .mdata _ b           => go b                               -- drop metadata
    | .proj t i s          => s!"R({encodeName t},{i},{go s})"
  go e

/-- Build the universe-parameter index map for a constant's `levelParams`. -/
private def buildParamIdx (levelParams : List Name) : Std.HashMap Name Nat :=
  levelParams.zipIdx.foldl (init := ∅) fun m (n, i) => m.insert n i

private def buildEntry (info : ConstantInfo) : CoreM Lsp.DeclManifestEntry := do
  let axs ← Lean.collectAxioms info.name
  let axStrs := axs.map toString |>.qsort (· < ·)
  let hasSorry := axStrs.contains (toString ``sorryAx)
  let paramIdx := buildParamIdx info.levelParams
  return {
    name := info.name.toString
    kind := Common.kindToString info
    typeRepr := Expr.canonical paramIdx info.type
    levelParams := info.levelParams.toArray.map toString
    axioms := axStrs
    hasSorry
  }

open RequestM in
def handleDeclManifest (_ : Lsp.DeclManifestParams)
    : RequestM (RequestTask Lsp.DeclManifest) :=
  -- Shared scaffolding: wait for elaboration, fold `buildEntry` over the
  -- module-local user constants of the post-elaboration env. The DeclManifest-
  -- specific part is just `buildEntry` (the canonical-`typeRepr` fingerprint).
  Common.handleSnapshotRequest
    (collect := do return { entries := ← Common.foldUserConstants buildEntry (·.name) })
    (empty := { entries := #[] })

initialize
  registerLspRequestHandler
    "$/lean/declManifest"
    Lsp.DeclManifestParams
    Lsp.DeclManifest
    handleDeclManifest

end WorkerPlugins.DeclManifest
