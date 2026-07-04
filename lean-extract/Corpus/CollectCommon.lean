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

end Corpus.CollectCommon
