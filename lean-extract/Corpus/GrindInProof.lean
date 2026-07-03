/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean
import Corpus.CollectCommon
import Corpus.Frontend
import Corpus.GrindManifest

/-!
`$/lean/grindInProof`: a FileWorker request that captures grind data from the
`grind` calls that occur INSIDE existing proofs — one record per grind CALL SITE
(verification condition), rather than re-proving whole theorem statements.

# Why

`WorkerPlugins.GrindManifest` re-proves each theorem's whole `type` with grind.
That is useless for tactic-heavy corpora (e.g. `mvcgen`) where `grind` never
proves the whole statement — it only discharges the subgoals a preceding tactic
emits (`mvcgen … with grind`, `all_goals mleave <;> grind`, `grind [lemmas]`).
The interesting grind moves live on those mid-proof subgoals, which the
whole-statement mode never sees.

This plugin instead OBSERVES grind where it actually runs: it walks each
command's `InfoTree`, finds every `TacticInfo` node whose syntax is a real
`Lean.Parser.Tactic.grind` call, restores the goal state grind saw
(`mctxBefore` / `goalsBefore`), and RE-RUNS the instrumented grind pipeline on
that captured goal — using the AUTHOR'S hint params (`grind [lemmas]` / `only`).
For each call site it records the same AlphaGo-style triple + interactive
script the whole-statement mode captures, plus the call-site location, the
enclosing theorem, and the author's hint set.

# Scope

DIRECT grind tactic nodes only: `<;> grind`, `grind [..]`, `by grind`,
`all_goals grind`. The fused `mvcgen … with grind` one-liner is deliberately NOT
captured: that grind runs inside the `mvcgen` elaborator (it parses `with grind`
into `Grind.Params` and calls grind programmatically), so it never appears as a
`Lean.Parser.Tactic.grind` tactic node and the walk naturally excludes it.

# How

Everything runs at `MetaM`/`TermElabM`/`GrindM` (no `TacticM`). Per grind node:

1. Restore the before-state: `{ctx with mctx := ti.mctxBefore}.runMetaM {} …`.
2. Take `goal := ti.goalsBefore.head?` (each `all_goals`/`<;>` invocation is its
   own `TacticInfo` with a single-goal `goalsBefore`, so this is per-VC).
3. Read the author's `only` flag + `[..]` hint params off `ti.stx`.
4. Build `params` via `mkGrindParams` (in `TermElabM`, inside `goal.withContext`)
   using the instrumented `mkGrindConfig` — so the seq/triple are captured and
   the author hints become part of the ematch set for the run.
5. Delegate to `GrindManifest.runGrindCore` (shared with the whole-statement
   mode): default finish strategy, `.stuck` sentinel dance, triple extraction.
-/

namespace Corpus

open Lean

/-- One in-proof grind call site's outcome. -/
structure GrindInProofEntry where
  /-- Fully-qualified name of the enclosing theorem/def (from the InfoTree
  `parentDecl?`), or `""` if unknown. -/
  enclosingTheorem : String
  /-- The module that elaborated the enclosing declaration (the file under study). -/
  module      : String
  /-- 1-based source line of the `grind` call, or `none`. -/
  startLine   : Option Nat
  /-- 0-based source column of the `grind` call, or `none`. -/
  startCol    : Option Nat
  /-- Pretty-printed goal (the restored VC) grind was re-run on. -/
  goalType    : String
  /-- The author's hint params rendered as written, e.g. `"[List.nodup_cons]"`;
  `none` if the source `grind` had no `[..]` clause. -/
  authorHints : Option String
  /-- `true` iff the source call was `grind only …`. -/
  authorOnly  : Bool
  /-- `"closed"` / `"stuck"` / `"error"` / `"deadline_skipped"`. -/
  outcome     : String
  /-- The `grind => <seq>` interactive script (rendered), when `outcome=closed`. -/
  interactive : Option String
  /-- The `grind only [...]` reconstruction (rendered), when `outcome=closed`. -/
  grindOnly   : Option String
  /-- `true` iff grind's generated seq contained `sorry` (artifacts suppressed). -/
  hasSorry    : Bool
  /-- Origins grind ACTIVATED with counts, `"<name>:<count>"` (local origins
  prefixed `local:`/`stx:`). -/
  activated   : Array String
  /-- Global-`.decl` names whose instances appear in the final proof term. -/
  used        : Array String
  /-- Count of USED origins that were NOT global `.decl`s (non-portable reliance). -/
  coverageGap : Nat
  /-- `true` iff the enclosing declaration's name is `private`. -/
  isPrivate   : Bool
  deriving FromJson, ToJson

open Lean.Meta Lean.Meta.Grind Lean.Elab Lean.Elab.Tactic
-- `mkGrindConfig` / `runGrindCore` / `availableHintsPublic` / `grindHeartbeats` /
-- `runGrindGuarded` are siblings in `namespace Corpus` (from `Corpus.GrindManifest`),
-- so they resolve directly here without an `open`.

/-! ## Grind-node collection

We collect every `TacticInfo` node whose syntax is a real `grind` tactic. We do
NOT dedup by source range: combinators like `all_goals`/`<;>` re-invoke
`evalTactic` on the SAME grind syntax once per goal, producing N distinct
`TacticInfo` nodes each with a single-goal `goalsBefore` — that is exactly the
per-VC granularity we want, so collapsing by range would lose real subgoals. -/

/-- A captured grind call site: the enclosing context + the tactic info. -/
structure GrindSite where
  ctx : ContextInfo
  ti  : TacticInfo

/-- Fold one command `InfoTree`, pushing a `GrindSite` for every `TacticInfo`
whose `stx` is of kind `Lean.Parser.Tactic.grind`. -/
private def collectGrindSites (tree : InfoTree) : Array GrindSite :=
  tree.foldInfo (init := #[]) fun ctx info acc =>
    match info with
    | .ofTacticInfo ti =>
      if ti.stx.getKind == ``Lean.Parser.Tactic.grind then
        acc.push { ctx, ti }
      else acc
    | _ => acc

/-! ## Reading the author's hints off the grind syntax

Grind syntax layout (`Init/Grind/Tactics.lean`):
`grind`(0) `optConfig`(1) `only`(2) `[params]`(3) `=> seq`(4). -/

/-- `true` iff the source call was `grind only …` (child [2] present). -/
private def sourceIsOnly (stx : Syntax) : Bool :=
  !stx[2].isNone

/-- The author's `[..]` hint param syntaxes (child [3], the separated args),
retyped for `mkGrindParams`. Empty when there is no `[..]` clause. -/
private def sourceGrindParams (stx : Syntax) : TSyntaxArray ``Lean.Parser.Tactic.grindParam :=
  (stx[3][1].getSepArgs).map (⟨·⟩)

/-- Render the author's hint clause as written, e.g. `"[List.nodup_cons]"`, or
`none` if there were no hints. Best-effort via `Syntax.reprint`; a render failure
falls back to `none` rather than losing the record. -/
private def renderAuthorHints (ps : TSyntaxArray ``Lean.Parser.Tactic.grindParam)
    : Option String :=
  if ps.isEmpty then none
  else
    let parts := ps.filterMap (·.raw.reprint)
    if parts.isEmpty then none
    else some s!"[{String.intercalate ", " (parts.map (·.trimAscii.copy)).toList}]"

/-! ## The per-site grind re-run

Mirrors the real `grind` tactic (lowered from `TacticM` to `MetaM`): restore the
before-state, build params from the author's hints under the goal's context, and
delegate to the shared `runGrindCore`. -/

/-- Re-run instrumented grind on one captured goal `mvarId` using the author's
`only`/`[..]` hints. Runs entirely in `MetaM` on an ALREADY-RESTORED mctx (the
caller sets `mctx := ti.mctxBefore` via `ContextInfo.runMetaM`). Returns the core
`GrindManifestEntry` (name/module/range filled by the caller). -/
private def rerunGrindOnGoal (mvarId : MVarId) (only : Bool)
    (authorPs : TSyntaxArray ``Lean.Parser.Tactic.grindParam)
    : MetaM GrindManifestEntry := do
  let config := mkGrindConfig
  -- `mkGrindParams` runs in `TermElabM` (it resolves hint idents/terms, possibly
  -- against the goal's local hypotheses) and MUST see the goal's local context —
  -- so build params inside `mvarId.withContext`. We pass our INSTRUMENTED config
  -- in (not the author's optConfig, which is `TacticM`-only and unreachable here):
  -- only the author's hint theorems + `only` flag are borrowed.
  let goalTypeStr := ((← Meta.ppExpr (← mvarId.getType)).pretty 100).trimAsciiEnd.copy
  let params ← mvarId.withContext do
    let p ← Term.TermElabM.run' (mkGrindParams config only authorPs mvarId)
    -- Mirror the real tactic's markInstances guard (a no-op here since
    -- mkGrindConfig already sets markInstances := true, but kept for parity).
    if grind.unusedLemmaThreshold.get (← getOptions) > 0 then
      pure { p with config.markInstances := true }
    else pure p
  -- Bound this VC by the finite `grindHeartbeats` backstop (same as the whole-
  -- statement path); a runaway grind degrades to `stuck`. The caller's own
  -- `tryCatchRuntimeEx` is a second net for a throw from the prologue above.
  runGrindGuarded { goalType := goalTypeStr, outcome := "stuck",
                    interactive := none, grindOnly := none, hasSorry := false,
                    name := "", module := "", activated := #[], used := #[],
                    coverageGap := 0, startLine := none, isPrivate := false }
    (runGrindCore goalTypeStr mvarId params)

/-! ## The file-level walk -/

/-- Walk every command `InfoTree` for grind call sites and re-run grind on each,
under a per-file wall-clock budget (cheap tail-shedding, like `GrindManifest`).
`deadlineMs = 0` disables the budget. `trees` is the file's per-command InfoTrees
(from `Frontend.ElabResult.trees`, one per post-header command). Runs in the
file's post-elaboration `CoreM`; each site's re-run re-enters `MetaM` on the
restored `ctx`. -/
private def foldGrindSites (trees : Array Elab.InfoTree) (includePrivate : Bool)
    (deadlineMs : Nat) : CoreM (Array GrindInProofEntry) := do
  -- Collect sites across all command trees first (cheap; blocks on lazy info).
  let mut sites : Array GrindSite := #[]
  for tree in trees do
    sites := sites ++ collectGrindSites tree
  let startMs ← IO.monoMsNow
  let mut out : Array GrindInProofEntry := #[]
  for site in sites do
    let ctx := site.ctx
    let ti := site.ti
    -- Location + author metadata (cheap, done regardless of deadline).
    let pos? := (ti.stx.getPos? (canonicalOnly := true)).map ctx.fileMap.toPosition
    let startLine := pos?.map (·.line)
    let startCol  := pos?.map (·.column)
    let enclosing := (ctx.parentDecl?.map (·.toString)).getD ""
    let isPriv := match ctx.parentDecl? with
      | some n => Lean.isPrivateName n
      | none   => false
    let authorPs := sourceGrindParams ti.stx
    let only := sourceIsOnly ti.stx
    let authorHints := renderAuthorHints authorPs
    -- Skip private-enclosed sites when requested.
    if !includePrivate && isPriv then
      continue
    let base : GrindInProofEntry := {
      enclosingTheorem := enclosing, module := ctx.env.mainModule.toString,
      startLine, startCol, goalType := "", authorHints, authorOnly := only,
      outcome := "error", interactive := none, grindOnly := none,
      hasSorry := false, activated := #[], used := #[], coverageGap := 0,
      isPrivate := isPriv }
    -- Past the budget: keep a placeholder, don't run grind.
    let attempt := deadlineMs == 0 || (← IO.monoMsNow) - startMs < deadlineMs
    if !attempt then
      out := out.push { base with outcome := "deadline_skipped" }
      continue
    -- The one goal this grind invocation ran on. Under all_goals/<;> this is a
    -- single-element list. Skip empty (grind reached with no goals) or a goal
    -- already assigned in the restored mctx (recovery/ill-formed node).
    let some mvarId := ti.goalsBefore.head? | continue
    let ciBefore := { ctx with mctx := ti.mctxBefore }
    -- Re-enter MetaM on the restored before-state. Guard the WHOLE per-site run
    -- so a single pathological site degrades to one `error` record rather than
    -- aborting the file. `runGrindCore` only guards grind EXECUTION; the prologue
    -- here (`Meta.ppExpr`, `mvarId.getType`, and — critically — `mkGrindParams`,
    -- which elaborates the author's hint terms against the restored goal and can
    -- throw when we drop the author's optConfig / a hint no longer resolves) runs
    -- BEFORE that guard. We use `tryCatchRuntimeEx` (not a plain `try`) so a grind
    -- run that exhausts `maxHeartbeats`/recursion depth (a RUNTIME exception,
    -- which `runGrindCore`'s `MonadExcept` catch deliberately rethrows) is also
    -- contained to this one site. Interrupts (Ctrl-C) still propagate. This runs
    -- inside `runMetaM`, so the exception is still a classified `Lean.Exception`
    -- (before the `.toIO` boundary), which is what `tryCatchRuntimeEx` needs. -/
    let entry ← ciBefore.runMetaM {} do
      tryCatchRuntimeEx
        (do
          if (← mvarId.isAssigned) then
            return { base with outcome := "error" }
          let e ← rerunGrindOnGoal mvarId only authorPs
          return { base with
            goalType := e.goalType, outcome := e.outcome,
            interactive := e.interactive, grindOnly := e.grindOnly,
            hasSorry := e.hasSorry, activated := e.activated, used := e.used,
            coverageGap := e.coverageGap })
        (fun _ => pure { base with outcome := "error" })
    out := out.push entry
  return out

/-- The in-process in-proof grind entry point: for one frontend-elaborated file,
walk its InfoTrees for `grind` call sites, re-run instrumented grind on each
restored VC, and return the env-wide `available` hint set plus one entry per call
site. Replaces the `$/lean/grindInProof` request handler — same `CoreM` walk, run
via `Frontend.runCollectorOn` against `r`'s environment and InfoTrees.

`grindDeadlineMs` bounds the WHOLE per-file walk (cheap tail-shed to
`deadline_skipped`); the per-VC `grindHeartbeats` backstop bounds each re-run. -/
def grindInProofCore (r : Frontend.ElabResult) (includePrivate : Bool)
    (grindDeadlineMs : Nat := 0) : IO (Array String × Array GrindInProofEntry) :=
  Frontend.runCollectorOn r do
    let env ← getEnv
    let available := availableHintsPublic env
    let entries ← foldGrindSites r.trees.toArray includePrivate grindDeadlineMs
    return (available, entries)

/-- Public wrapper over `rerunGrindOnGoal` (re-run grind on one captured VC). -/
def rerunGrindOnGoalPublic (mvarId : MVarId) (only : Bool)
    (authorPs : TSyntaxArray ``Lean.Parser.Tactic.grindParam)
    : MetaM GrindManifestEntry := rerunGrindOnGoal mvarId only authorPs

end Corpus
