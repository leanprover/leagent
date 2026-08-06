/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanReassemble.Rewrite

/-!
`LeanReassemble.Manifest` — the per-theorem action override map.

A manifest is a SPARSE override on top of the global `--proofs` mode: it names
only the theorems whose action differs from the default. Every theorem it does
not mention falls back to `--proofs`. So an empty manifest is a no-op and the
tool behaves exactly as before.

The manifest carries no dependency analysis. If it deletes a theorem that others
reference, the resulting build failure is the caller's to own (see `ProofMode`).
-/

namespace LeanReassemble

open Lean

/-- A sparse map from full theorem name to the action to take on it. Absent names
fall back to the run's `--proofs` mode. -/
structure Manifest where
  actions : Std.HashMap String ProofMode
  deriving Inhabited

namespace Manifest

/-- The empty manifest: every theorem follows the global `--proofs` mode. -/
def empty : Manifest := { actions := {} }

/-- The effective action for `name`: its manifest override, or `default`. -/
def actionFor (manifest : Manifest) (name : String) (default : ProofMode) : ProofMode :=
  manifest.actions.getD name default

/-- Parse one action string. Mirrors `Main.parseProofMode` so a manifest value and
a `--proofs` value name the same set of actions. -/
private def parseAction : String → Except String ProofMode
  | "sorry"  => .ok .replace
  | "keep"   => .ok .keep
  | "delete" => .ok .delete
  | value    => .error s!"expects keep|sorry|delete, got: {value}"

/-- Decode a manifest from JSON.

```json
{ "format": "lean-reassemble-manifest.v1",
  "theorems": { "Foo.bar": "delete", "Foo.baz": "keep" } }
```

The `theorems` object's keys are theorem names and its values are actions. The
`format` key is accepted for forward compatibility but not required. -/
def fromJson? (j : Json) : Except String Manifest := do
  let theorems ← match j.getObjVal? "theorems" with
    | .ok (Json.obj kvs) => pure kvs
    | .ok _ => .error "manifest `theorems` must be a JSON object"
    | .error _ => .error "manifest is missing a `theorems` object"
  -- Fold the object's key/value pairs into the action map, short-circuiting on the
  -- first malformed entry. `RBNode.foldl` visits keys in sorted order, so the error
  -- reported is deterministic.
  theorems.foldl (init := .ok { actions := {} }) (fun acc name value =>
    match acc with
    | .error e => .error e
    | .ok manifest =>
      match value with
      | Json.str action =>
        match parseAction action with
        | .ok mode => .ok { actions := manifest.actions.insert name mode }
        | .error e => .error s!"manifest action for {name} {e}"
      | _ => .error s!"manifest action for {name} must be a string")

/-- Read and decode a manifest file. -/
def read (path : System.FilePath) : IO Manifest := do
  let content ← IO.FS.readFile path
  match Json.parse content with
  | .error e => fail s!"{path}: malformed manifest JSON: {e}"
  | .ok json =>
    match fromJson? json with
    | .ok manifest => return manifest
    | .error e => fail s!"{path}: {e}"

/-- Reject manifest keys that name no eligible theorem — a typo guard. `eligible`
is the set of theorem names the run will actually consider. -/
def validateKeys (manifest : Manifest) (eligible : Std.HashSet String) : IO Unit := do
  let mut unknown : Array String := #[]
  for name in manifest.actions.keys do
    unless eligible.contains name do
      unknown := unknown.push name
  unless unknown.isEmpty do
    fail s!"manifest names theorem(s) absent from the records: \
      {", ".intercalate unknown.qsort.toList}"

end Manifest

end LeanReassemble
