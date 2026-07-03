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
file under elaboration (not imported) and is not an elaboration-private detail
name (`_aux`, `match_…`, equation-compiler shards, …).

`getModuleIdxFor? name |>.isNone` is the local/imported discriminator: it reads
`const2ModIdx`, which is populated only at import time (`finalizeImport`) and
never during command elaboration — so the file's own new constants are absent
(→ `none`) while every imported constant (core/Std AND sibling project modules)
has an index. This holds identically whether the file is imported (legacy path)
or elaborated in-process via the frontend. -/
def isUserConstant (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).isNone && !name.isInternalDetail

end Corpus.CollectCommon
