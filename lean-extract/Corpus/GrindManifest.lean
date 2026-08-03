/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Paul Govereau
-/
import Lean
import Corpus.CollectCommon
import Corpus.Options
import Corpus.Frontend
import Corpus.Verify

/-!
`$/lean/grindManifest`: a FileWorker request that, for each theorem in the
elaborated file, RE-PROVES the theorem with `grind`'s default strategy and
reports what `grind` did — the AlphaGrind data-collection primitive.

# Why

We are gathering training data for a model that suggests `grind` hints. `grind`
is a saturation prover: its "tree search" is E-matching + case-splits + theory
solvers, and its "moves" are E-matching theorem instantiations. For each proof
`grind` closes, this plugin captures, from ONE grind run, the full AlphaGo-style
triple plus BOTH replayable artifacts:

- `interactive` — the `grind => <seq>` script: the exact sequence of moves
  (`instantiate`/`use [thms]`, `cases`, `lia`/`ring`/…) that closes the goal,
  pre-minimized by `grind`'s CPS search to the steps that mattered. This is the
  PRIMARY training target (train the model to generate interactive proofs).
- `grind_only` — the `grind only [lemmas]` reconstruction: the flat lemma-hint
  set, extracted from the same seq. The secondary/declarative target.
- `available` — every `@[grind]` E-matching theorem active in the file's env
  (legal moves). Computed once per file (env-level), not per goal.
- `activated` — `[(origin, count)]`: every theorem grind's search instantiated,
  with frequency (moves the search explored). From `Result.counters.thm`.
- `used` — the origins that actually appear in the final proof term (the winning
  line). Recovered by walking the assigned proof for `markInstances` markers.

# How

Everything runs at the `MetaM`/`GrindM` level (no `TacticM`): we mirror what
`grind?`'s `evalFinishTrace`/`evalGrindTraceCore` do, but drive the default
strategy `Action.mkFinish` directly. Per theorem:

1. Build a fresh goal mvar from the theorem's `type`.
2. `withProtectedMCtx` + `GrindM.runAtGoal` to enter `GrindM` on that goal.
3. `(← Action.mkFinish).run goal` under `config.trace := true` (so the seq is
   logged) and `useSorry := false` (so a stuck goal is `.stuck`, never a
   sorry-laced `.closed`) and `markInstances := true` (so used-origins are
   recoverable).
4. On `.closed seq`: render `mkGrindSeq seq` (interactive) and
   `mkGrindOnlyTactics`/`mkFinishTactic` (grind-only), read `Result.counters`
   (activated), and walk the proof term for used-origins.

Grind sees the file's TRUE post-elaboration context — the real imported `@[grind]`
set, instances, `open`s. This is a SIBLING of `CorpusManifest`, not an extension:
it re-proves rather than reads existing proofs.
-/

namespace Corpus

open Lean

/-- One theorem's grind outcome in the manifest. -/
structure GrindManifestEntry where
  /-- Fully-qualified theorem name. -/
  name        : String
  /-- The module that elaborated this theorem (the file under study). -/
  module      : String
  /-- Pretty-printed goal type grind was run on. -/
  goalType    : String
  /-- `"closed"` (grind proved it), `"stuck"` (grind ran but could not close),
  `"error"` (grind threw), or `"deadline_skipped"` (past the per-file budget;
  not attempted). -/
  outcome     : String
  /-- The `grind => <seq>` interactive script (rendered), when `outcome=closed`.
  This is the PRIMARY training label. `none` otherwise, or if the seq contained
  `sorry`. -/
  interactive : Option String
  /-- The `grind only [...]` reconstruction (rendered), when `outcome=closed`.
  The secondary/declarative label. May be two variants (anchor-restricted and
  not); we keep the first (anchor-restricted if anchors exist). -/
  grindOnly   : Option String
  /-- `true` iff `grind`'s generated seq contained `sorry` (so both artifacts are
  suppressed — the "proof" is not real). Should not happen with useSorry:=false,
  but recorded defensively. -/
  hasSorry    : Bool
  /-- Origins (as strings) of theorems grind's search ACTIVATED, with counts —
  every candidate move the search explored. From `Result.counters.thm`. Each is
  `"<name>:<count>"` for `.decl` origins; local origins are prefixed `local:`. -/
  activated   : Array String
  /-- Fully-qualified names of theorems whose instances appear in the final proof
  term — the moves in the winning line (`.decl` origins only; portable). -/
  used        : Array String
  /-- Count of USED origins that were NOT global `.decl`s (proof-local
  hypotheses / stx args). A nonzero value flags that the proof leaned on
  non-portable facts; a zero-`used`, closed proof with `coverageGap=0` and no
  activated theorems means grind closed it purely by theory solvers / congruence
  (no lemma hints apply). -/
  coverageGap : Nat
  /-- 1-based start line of the theorem's source range, or `none`. -/
  startLine   : Option Nat
  /-- `true` iff the theorem's name is `private`. -/
  isPrivate   : Bool

open Lean.Meta Lean.Meta.Grind

/-! ## Eligibility: which theorems to run grind on

We only attempt real, source-authored theorems: `thmInfo` with a declaration
range (excludes synthetic `.injEq`/`.sizeOf_spec`/…), not an internal detail,
not a generated companion. This mirrors `CorpusManifest`'s `corpusEligible` for
theorems, so the grind dataset lines up with the corpus dataset by `name`. -/


/-- Keep iff this is a source-authored theorem grind should attempt. -/
private def grindEligible (_env : Environment) (includePrivate : Bool)
    (name : Name) (info : ConstantInfo) : CoreM Bool := do
  match info with
  | .thmInfo _ =>
    if name.isInternalDetail then return false
    if CollectCommon.hasGeneratedTag name || CollectCommon.isGeneratedTheoremSuffix name then return false
    if !includePrivate && Lean.isPrivateName name then return false
    -- Range-less synthetic theorems (`.injEq`, `.brecOn`, …) have no authored goal.
    return (← Lean.findDeclarationRanges? name).isSome
  | _ => return false

/-! ## Used-origin recovery

Re-implementation of grind's private `collectUsedOrigins`
(`Meta/Tactic/Grind/Main.lean`): walk the (instantiated) proof term and collect
the `Origin`s of E-matching instances that appear, via the `mdata` markers
`markInstances` places (public `EMatch.isTheoremInstanceProof?` +
`EMatch.InstanceMap`). We only need this map for the run's own instances. -/

private partial def collectUsedOrigins (e : Expr) (map : EMatch.InstanceMap)
    : Std.HashSet Grind.Origin :=
  (go e |>.run ({}, {})).2.2
where
  go (e : Expr) : StateM (Std.HashSet Sym.ExprPtr × Std.HashSet Grind.Origin) Unit := do
    -- Dedup on the hash-consed pointer, exactly as grind's own collectUsedOrigins.
    if (← get).1.contains ⟨e⟩ then return ()
    modify fun (v, o) => (v.insert ⟨e⟩, o)
    if let some uniqueId := EMatch.isTheoremInstanceProof? e then
      if let some thm := map[uniqueId]? then
        modify fun (v, o) => (v, o.insert thm.origin)
    match e with
    | .lam _ d b _
    | .forallE _ d b _ => go d; go b
    | .proj _ _ b
    | .mdata _ b       => go b
    | .letE _ t v b _  => go t; go v; go b
    | .app f a         => go f; go a
    | _ => return ()

/-- Format an `Origin` as a portable global name, else `none`. -/
private def originDeclName? : Grind.Origin → Option String
  | .decl declName => some declName.toString
  | _              => none

/-- Format an `Origin` for the `activated` list (keeps local origins, tagged). -/
private def originLabel : Grind.Origin → String
  | .decl declName => declName.toString
  | .fvar fvarId   => s!"local:{fvarId.name}"
  | .stx id _      => s!"stx:{id}"
  | .local id      => s!"local:{id}"

/-! ## Rendering grind syntax to text -/

/-- Render an interactive `grindSeq` to a one-line-ish string. -/
private def ppGrindSeq (seq : TSyntax ``Lean.Parser.Tactic.Grind.grindSeq) : CoreM String := do
  let fmt ← PrettyPrinter.ppCategory ``Lean.Parser.Tactic.Grind.grindSeq seq
  return (fmt.pretty 100).trimAsciiEnd.copy

/-- Render a top-level `grind only [...]`/`finish only [...]` tactic to a string. -/
private def ppTactic (tac : TSyntax `tactic) : CoreM String := do
  let fmt ← PrettyPrinter.ppCategory `tactic tac
  return (fmt.pretty 100).trimAsciiEnd.copy

/-- Run a renderer, returning `none` (not throwing) if the pretty-printer
backtracks. The grind syntax category can trip the parenthesizer on some steps;
a rendering failure must never discard an otherwise-successful proof. -/
private def tryRender (r : CoreM String) : CoreM (Option String) :=
  (some <$> r) <|> pure none

/-- An empty `optConfig` syntax node (no config items). -/
private def emptyOptConfig : CoreM (TSyntax ``Lean.Parser.Tactic.optConfig) :=
  return ⟨mkNode ``Lean.Parser.Tactic.optConfig #[mkNullNode #[]]⟩

/-! ## The per-theorem grind run

Mirrors `evalFinishTrace` (`Elab/Tactic/Grind/Trace.lean`) but at MetaM level and
against the DEFAULT strategy: build a fresh goal from the theorem type, enter
`GrindM` on it, run the finish strategy under a trace config, read the result. -/

/-- Config for data-collection grind runs: trace on (log the seq), no sorry
(stuck stays stuck), mark instances (recover used origins), quiet. Public so the
sibling in-proof collector (`Corpus.GrindInProof`) builds params against the
same instrumented flags. -/
def mkGrindConfig : Grind.Config :=
  { trace := true, useSorry := false, markInstances := true, verbose := false }

/-- Finite per-goal grind backstop, in RAW heartbeats (the `maxHeartbeats` option
is ×1000). This is the IN-PROCESS replacement for the killable worker: grind polls
`checkSystem "grind"` against `Core.Context.maxHeartbeats` throughout its search,
so a runaway grind run throws `runtime.maxHeartbeats` instead of pinning a thread
unbounded. Applied by the callers (`runGrindGuarded`) under a fresh heartbeat
baseline so it bounds each goal independently.

Sized in the same family as `ReverseElab`'s `verifyHeartbeats` (4M) /
`reverseHeartbeats` (12M): grind's default ceiling is 200k
(`Elab.async`-era default ×1000), so 2M ≈ 10× default — generous enough that every
goal that closes or genuinely saturates does so identically (a run well under the
cap sees NO change in outcome), while a pathological goal is bounded. The per-file
`grindDeadlineMs` wall-clock guard remains the PRIMARY latency bound (heartbeats
track work, not wall time); this is the backstop for a single goal that would spin
without the fold ever regaining control. Re-measure against corpus tails. -/
def grindHeartbeats : Nat := 2000000

/-- Run `act` (a `runGrindCore` call) under the finite `grindHeartbeats` per-goal
backstop. `withCurrHeartbeats` resets the baseline so the cap is measured from the
start of THIS run (not the file-wide accumulation), and `tryCatchRuntimeEx` catches
the `runtime.maxHeartbeats`/recursion throw that grind emits when the cap is hit —
which `runGrindCore`'s own bare `catch` deliberately rethrows (runtime exceptions
are not caught by ordinary `MonadExcept`). On a timeout we return `fallback`
(outcome `stuck`: grind genuinely could not close the goal within its budget). A
goal that finishes under the cap is unaffected, so outcomes are unchanged except
for the runaway tail this is meant to bound. -/
def runGrindGuarded (fallback : GrindManifestEntry) (act : MetaM GrindManifestEntry)
    : MetaM GrindManifestEntry :=
  withCurrHeartbeats <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := grindHeartbeats }) <|
    tryCatchRuntimeEx act (fun _ => pure fallback)

/-- `grind`'s default finish strategy, but WITHOUT the leading
`Action.checkTactic` that `Action.mkFinish` prepends. That check *replays* the
generated seq via `evalTactic` to self-verify it — but we run grind with
`evalTactic? := none` (`EvalTactic.skip`, since we have no `TacticM`), so the
replay can never interpret grind steps and always "fails", emitting a spurious
`generated tactic cannot close the goal` warning PER theorem. The check is
advisory (`warnOnly`) and does not affect the returned proof, so dropping it is
sound; we run our own replay-based verification downstream instead. Body copied
from `Meta/Tactic/Grind/Finish.lean:mkFinish`. -/
private def mkFinishNoCheck (maxIterations : Nat := Action.maxIterationsDefault) : IO Action := do
  let solvers ← Solvers.mkAction
  let step : Action := solvers <|> Action.instantiate <|> Action.splitNext <|> Action.mbtc
  return Action.intros 0 >> Action.assertAll >> step.loop maxIterations

/-- The goal- and param-agnostic core of a data-collection grind run. Given a
pretty-printed `goalTypeStr`, a goal mvar `goalMVar`, and fully-built `params`
(whose `config` carries the instrumentation flags — see `mkGrindConfig`), drive
grind's default finish strategy on the goal and extract the entry payload (sans
the name/module/range fields, filled by the caller). On any grind exception,
returns an `error` outcome rather than propagating (one bad goal never aborts the
fold).

This works for BOTH the whole-statement mode (a fresh `mkFreshExprSyntheticOpaqueMVar`
goal + default-extension params) AND the in-proof mode (a captured mid-proof mvar
living in a restored `mctx`, its lctx carrying the real hypotheses, + author-hint
params). `withProtectedMCtx` reads the passed mvar's type/lctx (via `withContext`)
and re-solves through its own fresh mvar, assigning the assembled proof back to
`goalMVar` — so the used-origin walk over `mkMVar goalMVar` works either way. The
CALLER is responsible for restoring the mctx and building params before calling
this. -/
def runGrindCore (goalTypeStr : String) (goalMVar : MVarId)
    (params : Grind.Params) : MetaM GrindManifestEntry := do
  let base : GrindManifestEntry := {
    name := "", module := "", goalType := goalTypeStr, outcome := Outcome.error,
    interactive := none, grindOnly := none, hasSorry := false,
    activated := #[], used := #[], coverageGap := 0, startLine := none,
    isPrivate := false }
  let config := params.config
  -- `withProtectedMCtx` runs grind on a fresh goal mvar and, ON SUCCESS, assigns
  -- the assembled proof to it — which lets us walk that term for used-origins.
  -- BUT when grind does NOT close the goal (a genuine `.stuck`), the mvar stays
  -- unassigned and `withProtectedMCtx`'s finalize throws "unresolved internal
  -- metavariable". The real `grind` tactic sidesteps this by THROWING on
  -- failure, which trips `withProtectedMCtx`'s handler (it `admit`s the mvar and
  -- rethrows). We do the same: on `.stuck` we stash a `stuck` record and throw a
  -- sentinel; the catch below recovers it. A genuine grind exception leaves the
  -- ref unset and is recorded as `error` (distinguishing real failures — which
  -- should be `stuck` — from tooling errors was the whole point). -/
  let out ← IO.mkRef (none : Option GrindManifestEntry)
  try
    withProtectedMCtx config goalMVar fun mvarId => do
      GrindM.runAtGoal mvarId params fun goal => do
        let a ← mkFinishNoCheck
        match (← a.run goal) with
        | .stuck _ =>
          out.set (some { base with outcome := Outcome.stuck })
          throwError "grind-manifest: stuck (sentinel)"
        | .closed seq => do
          -- Interactive artifact. Rendering is wrapped so a parenthesizer
          -- backtrack on an exotic step never loses the (successful) proof.
          let interactiveStr ← liftM <| tryRender (ppGrindSeq (Action.mkGrindSeq seq))
          -- grind-only artifact: prefer the anchor-restricted variant (index 0).
          let cfgStx ← liftM emptyOptConfig
          let onlyTacs ← liftM <| mkGrindOnlyTactics cfgStx seq
          let grindOnlyStr ← match onlyTacs[0]? with
            | some t => liftM (tryRender (ppTactic t))
            | none   => pure none  -- empty ⇒ seq had `sorry`
          let hasSorry := onlyTacs.isEmpty
          -- Triple: activated (counters) + used (proof-term markers).
          let result ← mkResult params (failure? := none)
          let activated := result.counters.thm.toList.toArray.map
            (fun (o, c) => s!"{originLabel o}:{c}")
          let instMap := (← getThe Grind.State).instanceMap
          -- Walk the INNER mvar grind assigned during `k` (the lambda param),
          -- NOT `goalMVar`: `withProtectedMCtx` only assigns the outer `goalMVar`
          -- AFTER this continuation returns, so at this point it is still
          -- unassigned. `mvarId` here is grind's fresh working mvar, now solved.
          let proof ← instantiateMVars (mkMVar mvarId)
          let usedOrigins := collectUsedOrigins proof instMap
          let mut used : Array String := #[]
          let mut gap := 0
          for o in usedOrigins do
            match originDeclName? o with
            | some n => used := used.push n
            | none   => gap := gap + 1
          out.set (some { base with
            outcome := Outcome.closed
            interactive := if hasSorry then none else interactiveStr
            grindOnly := if hasSorry then none else grindOnlyStr
            hasSorry
            activated := activated.qsort (· < ·)
            used := used.qsort (· < ·)
            coverageGap := gap })
    -- Closed path: the ref holds the full entry.
    return (← out.get).getD base
  catch _ =>
    -- Either our `.stuck` sentinel (ref already holds the stuck record) or a
    -- genuine grind exception (ref unset → `error`). One goal throwing never
    -- aborts the fold.
    match (← out.get) with
    | some e => return e
    | none   => return { base with outcome := Outcome.error }

/-- Run grind on one theorem `type` (whole-statement mode). Builds a fresh goal
from the type and default-extension params, then delegates to `runGrindCore`. -/
private def runGrindOn (type : Expr) : MetaM GrindManifestEntry := do
  let goalTypeStr := ((← (Meta.ppExpr type)).pretty 100).trimAsciiEnd.copy
  let config := mkGrindConfig
  let ext ← getDefaultExtensionState
  let params ← mkParams config #[ext]
  let goalMVar := (← mkFreshExprSyntheticOpaqueMVar type).mvarId!
  -- Bound this goal by the finite `grindHeartbeats` backstop; a runaway grind
  -- degrades to `stuck` rather than pinning the thread (the in-process substitute
  -- for the killable worker).
  runGrindGuarded { goalType := goalTypeStr, outcome := Outcome.stuck,
                    interactive := none, grindOnly := none, hasSorry := false,
                    name := "", module := "", activated := #[], used := #[],
                    coverageGap := 0, startLine := none, isPrivate := false }
    (runGrindCore goalTypeStr goalMVar params)

/-! ## The file-level fold -/

/-- The available-hint set: fully-qualified names of every `@[grind]` E-matching
theorem active in the environment (`.decl` origins). Env-level, computed once.
Shared with the in-proof collector. -/
def availableHints (env : Environment) : Array String := Id.run do
  let st := grindExt.getState env
  let mut out : Array String := #[]
  for o in st.ematch.getOrigins do
    if let some n := originDeclName? o then
      out := out.push n
  return (out.toList.eraseDups.mergeSort (· < ·)).toArray

/-- Fold `runGrindOn` over the eligible theorems under a per-file wall-clock
budget (cheap tail-shedding, like `CorpusManifest`). `deadlineMs = 0` disables
the budget. Emits one entry per eligible theorem, sorted by name. -/
private def foldGrindEntries (includePrivate : Bool) (deadlineMs : Nat)
    : MetaM (Array GrindManifestEntry) := do
  let env ← getEnv
  -- Source the file-local constants from the shared VERIFICATION substrate
  -- (`Verify.verifiedFileConstants`) rather than re-enumerating `env.constants`:
  -- grind-manifest is a CLIENT of the verification mechanism. Grind re-proves each
  -- statement from scratch (whole-statement self-play) and never touches the
  -- original proof term, so `isSorryFree` is NOT a filter here — every eligible
  -- theorem is attempted, matching the prior behavior exactly.
  let mut eligible : Array (Name × ConstantInfo) := #[]
  for vc in (← Corpus.Verify.verifiedFileConstants) do
    let name := vc.info.name
    if (← grindEligible env includePrivate name vc.info) then
      eligible := eligible.push (name, vc.info)
  let startMs ← IO.monoMsNow
  let mut out : Array GrindManifestEntry := #[]
  for (name, info) in eligible do
    let attempt := deadlineMs == 0 || (← IO.monoMsNow) - startMs < deadlineMs
    let ranges? ← Lean.findDeclarationRanges? name
    let startLine := ranges?.map (·.range.pos.line)
    let modStr := match env.getModuleIdxFor? name with
      | some idx => (env.allImportedModuleNames[idx.toNat]?).map toString |>.getD ""
      | none     => env.mainModule.toString
    let isPriv := Lean.isPrivateName name
    let entry ←
      if !attempt then
        let e : GrindManifestEntry :=
          { name := name.toString, module := modStr, goalType := "",
            outcome := Outcome.deadlineSkipped, interactive := none, grindOnly := none,
            hasSorry := false, activated := #[], used := #[], coverageGap := 0,
            startLine := startLine, isPrivate := isPriv }
        pure e
      else
        let e ← runGrindOn info.type
        pure { e with name := name.toString, module := modStr, startLine := startLine, isPrivate := isPriv }
    out := out.push entry
  return out.qsort (fun a b => a.name < b.name)

/-- The in-process grind-manifest entry point: for one frontend-elaborated file,
re-prove every eligible theorem with grind and return the env-wide `available`
hint set plus one entry per theorem. Replaces the `$/lean/grindManifest` request
handler — same `CoreM`/`MetaM` fold, run via `Frontend.runCollectorOn` against
`r`'s post-elaboration environment.

`grindDeadlineMs` bounds the WHOLE per-file fold (cheap tail-shed to
`deadline_skipped`); the per-goal `grindHeartbeats` backstop bounds each attempt.
The driver sets `grindDeadlineMs` below its own per-file timeout. -/
def grindManifestCore (r : Frontend.ElabResult) (includePrivate : Bool)
    (grindDeadlineMs : Nat := 0) : IO (Array String × Array GrindManifestEntry) :=
  Frontend.runCollectorOn r do
    let env ← getEnv
    let available := availableHints env
    let entries ← Meta.MetaM.run' (foldGrindEntries includePrivate grindDeadlineMs)
    return (available, entries)

end Corpus
