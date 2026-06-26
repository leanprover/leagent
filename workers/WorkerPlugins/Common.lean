/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean.Server.Requests
import Lean.Server.Snapshots
import Lean.Util.CollectAxioms

/-!
`WorkerPlugins.Common` — shared scaffolding for FileWorker introspection plugins
(`DeclManifest`, `CorpusManifest`, …).

Every such plugin has the same shape: an LSP request handler that waits for the
file's command snapshots to finish, grabs the post-elaboration environment from
the last snapshot, and folds a per-constant builder over the *module-local*
declarations (skipping imported constants and elaboration-private detail names).
Only the per-constant payload differs between plugins. This module factors out:

- `kindToString`           — `ConstantInfo` → stable kind label.
- `isUserConstant`         — the module-local + not-internal-detail filter.
- `foldUserConstants`      — fold a `CoreM` builder over filtered constants.
- `handleSnapshotRequest`  — the `readDoc`/`waitAll`/last-snapshot/`runCoreM`
                             plumbing, parameterized by a `CoreM` collector.

Each consumer plugin supplies its own params/response LSP types, its collector,
and its `registerLspRequestHandler` call.
-/

namespace WorkerPlugins.Common

open Lean Lean.Server Lean.Server.Snapshots Lean.Server.RequestM

/-- Stable kind label shared across plugins. -/
def kindToString : ConstantInfo → String
  | .axiomInfo _    => "axiom"
  | .thmInfo _      => "theorem"
  | .defnInfo _     => "definition"
  | .opaqueInfo _   => "opaque"
  | .inductInfo _   => "inductive"
  | .ctorInfo _     => "constructor"
  | .recInfo _      => "recursor"
  | .quotInfo _     => "quotient"

/-- A constant is "user-relevant" for introspection iff it was introduced by the
file under elaboration (not imported) and is not an elaboration-private detail
name (`_aux`, `match_…`, equation-compiler shards, …). -/
def isUserConstant (env : Environment) (name : Name) : Bool :=
  (env.getModuleIdxFor? name).isNone && !name.isInternalDetail

/-- Fold a `CoreM` per-constant builder over every user-relevant constant in the
current environment, returning the results sorted by the supplied key. The
builder runs in `CoreM` (so it may pretty-print, collect axioms, run `MetaM` via
`MetaM.run'`, etc.). -/
def foldUserConstants {α} (build : ConstantInfo → CoreM α) (sortKey : α → String)
    : CoreM (Array α) := do
  let env ← getEnv
  let mut out : Array α := #[]
  for (name, info) in env.constants.toList do
    if isUserConstant env name then
      out := out.push (← build info)
  return out.qsort (fun a b => sortKey a < sortKey b)

/-- The shared FileWorker request plumbing: wait for command snapshots, take the
last (post-elaboration) snapshot's environment, and run `collect` in its
`CoreM`. If elaboration produced no command snapshots (e.g. header-only file or
a parse failure before the first command), returns `empty`. -/
def handleSnapshotRequest {resp : Type} (collect : CoreM resp) (empty : resp)
    : RequestM (RequestTask resp) := do
  let doc ← readDoc
  let t := doc.cmdSnaps.waitAll
  mapTaskCheap t fun (snaps, _) => do
    let some last := snaps.reverse.head? | return empty
    RequestM.runCoreM last (liftM collect)

/-- Like `handleSnapshotRequest`, but additionally exposes the file's SOURCE text
and every per-command parsed `Syntax` to the collector. Plugins that reconstruct
source spans (signature/body) need the per-command `stx` (with absolute byte
positions into `doc.meta.text.source`) and the source string; the env-only
`handleSnapshotRequest` cannot provide those because it folds over
`env.constants` and never inspects per-command `stx`.

`collect` receives the full source string and the array of all command snapshots
(in file order; the first element is the header snapshot, the rest carry one
command `stx` each), and runs in the LAST snapshot's `CoreM` (so it sees the
post-elaboration environment, exactly like `handleSnapshotRequest`). -/
def handleSnapshotRequestWithSource {resp : Type}
    (collect : String → Array Snapshot → CoreM resp) (empty : resp)
    : RequestM (RequestTask resp) := do
  let doc ← readDoc
  let src := doc.meta.text.source
  let t := doc.cmdSnaps.waitAll
  mapTaskCheap t fun (snaps, _) => do
    let snapArr := snaps.toArray
    let some last := snapArr.back? | return empty
    RequestM.runCoreM last (liftM (collect src snapArr))

end WorkerPlugins.Common
