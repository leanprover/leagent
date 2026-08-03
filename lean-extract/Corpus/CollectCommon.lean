/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean
import Lean.Util.CollectAxioms

/-!
`Corpus.CollectCommon` — pure per-file collector scaffolding shared by the corpus
and grind collectors.

These are the version-agnostic helpers that used to live in
`WorkerPlugins.Common`. The LSP request plumbing that lived alongside them
(`handleSnapshotRequest` / `handleSnapshotRequestWithSource`) is GONE: it was the
worker-side glue that waited on `doc.cmdSnaps` and ran a collector in the last
snapshot's `CoreM`. In the single-process model that role is played by
`Corpus.Frontend.runCollectorOn`, which runs a `CoreM` collector directly against
the frontend-elaborated environment. Only the pure per-constant helpers remain:

- `kindToString`      — `ConstantInfo` → stable kind label.
- `isUserConstant`    — the file-local + not-internal-detail filter (keyed on
                        `getModuleIdxFor?`, which is `none` exactly for the
                        constants the file under study just elaborated).
-/

namespace Corpus.CollectCommon

open Lean

/-- Stable kind label shared across collectors. -/
def kindToString : ConstantInfo → String
  | .axiomInfo _    => "axiom"
  | .thmInfo _      => "theorem"
  | .defnInfo _     => "definition"
  | .opaqueInfo _   => "opaque"
  | .inductInfo _   => "inductive"
  | .ctorInfo _     => "constructor"
  | .recInfo _      => "recursor"
  | .quotInfo _     => "quotient"

/-- A constant is "user-relevant" for extraction iff it was introduced by the
file under elaboration (not imported) and is a name a user actually authored —
not an elaboration-private detail (`_aux`, `match_…`, equation-compiler shards, …).

`getModuleIdxFor? name |>.isNone` is the local/imported discriminator: it reads
`const2ModIdx`, which is populated only at import time (`finalizeImport`) and
never during command elaboration — so the file's own new constants are absent
(→ `none`) while every imported constant (core/Std AND sibling project modules)
has an index. This holds identically whether the file is imported (legacy path)
or elaborated in-process via the frontend.

PRIVATE declarations are user-authored but carry a mangled `_private.Mod.N.…`
name, which `Name.isInternalDetail` rejects (its leading `_private` component is
internal-or-num). We must NOT drop them: a proof frequently `rw`/`exact`s a
`private theorem` in the same file, so the corpus needs their statements (to
axiomatize under a resolvable name — see `privateUserName`). We therefore accept
a name when EITHER it is not an internal detail, OR it is a private name whose
UNMANGLED user name (`privateToUserName`) is itself not an internal detail (i.e.
a genuine authored private decl, not a private compiler shard like a private
`match_1`). `includePrivate` still gates whether they are ultimately emitted
downstream (`corpusEligible`/`grindEligible`); this only stops the shared filter
from discarding them before that choice. -/
def isUserConstant (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).isNone
    && (!name.isInternalDetail
        || (Lean.isPrivateName name && !(Lean.privateToUserName name).isInternalDetail))

/-- The RESOLVABLE display form of a constant name: private names are unmangled
from `_private.Mod.N.User.name` to `User.name` (`privateToUserName`), every other
name is unchanged. Used at every string-emitting boundary — a record's own `name`,
and the `deps`/`premises` that reference it — so the dataset never leaks the
gensym-mangled `_private.…` form. The mangled form is meaningless to a consumer
and un-citeable in assembled source (a proof refers to a private lemma by its
user name); this makes premise→record joins and lemma axiomatization line up. The
premise-cone GRAPH walk stays on raw `Name`s (see `collectPremises`); only the
final formatting unmangles, so dependency resolution is unaffected. -/
def displayName (name : Name) : Name :=
  if Lean.isPrivateName name then Lean.privateToUserName name else name

/-- Compiler-synthesized name fragments that slip past `isInternalDetail` but are
never corpus material (`._proof_*`, `._eq_*`, `._eqDef`, `._sunfold`, `._unfold`). -/
def hasGeneratedTag (n : Name) : Bool :=
  let s := n.toString
  let containsTag (tag : String) : Bool := (s.splitOn tag).length > 1
  containsTag "._proof_" || containsTag "._eq_" || containsTag "._eqDef"
    || containsTag "._sunfold" || containsTag "._unfold"

/-- Auto-generated `def` equation-compiler theorems (`eq_def`/`induct` suffix). -/
def isGeneratedTheoremSuffix : Name → Bool
  | .str _ s => s == "eq_def" || s == "induct"
  | _        => false

/-- Names always dropped from the corpus: aux recursors, noConfusion, anonymous,
generated-tag names, equation-compiler suffixes, projections. -/
def alwaysSkip (env : Environment) (n : Name) : Bool :=
  Lean.isAuxRecursor env n || Lean.isNoConfusion env n || n.isAnonymous
    || hasGeneratedTag n || isGeneratedTheoremSuffix n || env.isProjectionFn n

/-- The project root: the first component of the environment's main module name.
For `LeanSQLite.Basic` this is `LeanSQLite`. Used as the owned-module prefix. -/
def projectRoot (env : Environment) : Name :=
  let rec firstComponent : Name → Name
    | .str .anonymous s => .str .anonymous s
    | .num .anonymous n => .num .anonymous n
    | .str p _          => firstComponent p
    | .num p _          => firstComponent p
    | .anonymous        => .anonymous
  firstComponent env.mainModule

/-- True iff `n` is owned by the project under study: either defined by the file
being elaborated (no module index) or by an imported module sharing the project
root prefix. Excludes core/Std/Mathlib. -/
def isOwnedName (env : Environment) (root : Name) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | none     => true
  | some idx =>
    match env.allImportedModuleNames[idx.toNat]? with
    | some m => root == m || root.isPrefixOf m
    | none   => false

/-- The module that defines `n`, if the environment knows one. `none` means a
builtin or an unattached constant — for an imported environment, everything that
came from an `.olean` has an index. -/
def moduleOf? (env : Environment) (n : Name) : Option Name :=
  env.getModuleIdxFor? n |>.bind fun idx =>
    env.allImportedModuleNames[idx.toNat]?

/-- True iff `modName` sits under one of the `--modules` root prefixes.

This is the ROOT-PREFIX notion of ownership, used wherever the `--modules` roots
are the authority: single-declaration closure computation (`Corpus.DeclClosure`).
It differs from `isOwnedName`, which
keys on the elaborating file's own project root (`projectRoot`) and is what the
per-file collector uses for the `premises` field. The two agree for a single-root
project and diverge for a multi-root run; `--decl` records both in its
`metadata.json` so an artifact says which was applied. -/
def isOwnedModuleName (roots : Array Name) (modName : Name) : Bool :=
  roots.any fun root => root == modName || root.isPrefixOf modName

/-- Ownership predicate over CONSTANTS for the root-prefix notion: owned iff the
constant's defining module is under one of `roots`. Unattached constants are not
owned — they are core builtins, recovered through imports rather than records. -/
def isOwnedByRoots (env : Environment) (roots : Array Name) : Name → Bool :=
  fun n => match moduleOf? env n with
    | none   => false
    | some m => isOwnedModuleName roots m

/-- Transitive premise cone from an EXPLICIT seed: BFS over
`Environment.constants` following only constants for which `owned` returns true.
For each owned constant popped we enqueue its own direct deps (type ∪ value), so
an owned `def` in the cone drags in whatever its body needs. External or absent
constants are skipped. The result is owned-only and excludes `root`.

The seed is what distinguishes the two cones a caller may want:
  * `rootCi.getUsedConstantsAsSet.toArray` (type ∪ value) — the PROOF cone, i.e.
    everything needed to re-prove the declaration. This is `collectPremises`, the
    cone the `premises` dataset field reports.
  * `rootCi.type.getUsedConstantsAsSet.toArray` — the STATEMENT cone, i.e. only
    what is needed to *state* it. Used by single-declaration extraction to
    annotate each closure member (see `Corpus.DeclClosure`). -/
partial def collectPremisesFrom (env : Environment) (owned : Name → Bool)
    (root : Name) (seed : Array Name) : Array Name := Id.run do
  let mut visited : Std.HashSet Name := {}
  let mut queue   : Array Name := seed
  visited := visited.insert root
  let mut result  : Array Name := #[]
  while h : queue.size > 0 do
    let n := queue[queue.size - 1]
    queue := queue.pop
    if visited.contains n then continue
    visited := visited.insert n
    if owned n then
      result := result.push n
      if let some ci := env.find? n then
        for d in ci.getUsedConstantsAsSet.toArray do
          unless visited.contains d do
            queue := queue.push d
  return result

/-- Transitive premise cone: `collectPremisesFrom` seeded with `root`'s direct dep
set (type ∪ value), i.e. the PROOF cone. This is the cone the `premises` dataset
field reports. -/
def collectPremises (env : Environment) (owned : Name → Bool)
    (root : Name) : Array Name :=
  match env.find? root with
  | none        => #[]
  | some rootCi => collectPremisesFrom env owned root rootCi.getUsedConstantsAsSet.toArray

/-- The STATEMENT cone: `collectPremisesFrom` seeded from `root`'s TYPE only —
every owned constant needed to state `root`, excluding anything reachable only
through its proof/value. -/
def collectStatementPremises (env : Environment) (owned : Name → Bool)
    (root : Name) : Array Name :=
  match env.find? root with
  | none        => #[]
  | some rootCi => collectPremisesFrom env owned root rootCi.type.getUsedConstantsAsSet.toArray

/-- Build a `MetaM` runner over an environment and execute `act`. Only the
environment matters; all other contexts are default.

`maxHeartbeats := 0` disables the global deterministic-timeout budget: a batch
walk over an entire environment would otherwise trip the default 200k cumulative
ceiling partway through a large project. Per-proof verification cost is bounded
locally instead (see `ReverseElab.tryElab`), so removing the global ceiling does
not let any single proof hang. -/
def runMetaOnEnv {α} (env : Environment) (act : MetaM α) : IO α := do
  let coreCtx : Core.Context :=
    { fileName := "<corpus-extract>", fileMap := default, maxHeartbeats := 0 }
  let coreSt  : Core.State   := { env := env }
  let (a, _, _) ← act.toIO coreCtx coreSt
  return a

end Corpus.CollectCommon
