import Lean

/-!
Reverse-elaboration: mechanically turn a proof *term* (`Expr`) back into a
short *tactic script* drawn from a small vocabulary (`intro`, `exact`, `rfl`,
`cases`, `have`, `by_cases`), with a self-correcting verify-and-fallback loop so
the result is correct by construction.

The design rests on one robustness guarantee: every candidate script we emit is
re-elaborated against the original goal and `isDefEq`-checked against the
original proof term. If a decomposed script fails to reproduce the term, we
fall back to a less ambitious one, ending at `exact <delaborated term>` which
reproduces *any* proof. The `method` label records which rung of the ladder
won, so a consumer can honestly tell a real decomposition (`structural`,
`intro_exact`, `intro_rfl`) from a zero-decomposition whole-term `exact_whole`.

Verification is TWO-stage: the cheap in-memory `tryElab` (run the candidate
`Syntax` against a fresh goal) filters candidates, then `verifyRendered`
re-parses the rendered STRING and checks it elaborates defeq to the term. The
second stage is essential — `runTactic` is more permissive than fresh parsing
(e.g. about hygienic `case` tags), so a candidate can pass the first stage yet
produce a string that is not a valid proof. Checking the stored artifact closes
that gap, and lets recognizers be optimistic: an unsound emission is simply
rejected and falls back, never stored.

Tiers:
  * Tier-1 backbone — `intro` spine, `rfl`, leaf `exact`.
  * Tier-2 structural — `cases … with` (from `T.casesOn`), `have` (from
    `letFun`/`letE`), `by_cases`/`next` (from `dite`), each recursing into
    branches/bodies. Emitted only when the head matches; verified like any
    other candidate.
  * Tier-3 (omega/simp/rw/decide residue) is deliberately NOT reversed — those
    subterms are kept inside a verified `exact` (labeled `*_opaque`).

All API used here is verified against Lean 4.14.0 core sources (ported to 4.31).

Lives in `WorkerPlugins` (sibling to `Common`) so both the worker plugin
(`CorpusManifest`, running inside `lean --worker`) and the import-based
extractor (`lean-extract`'s `Corpus.Extract`, via a lake `require`) share one
source of truth — the verify-and-fallback soundness guards here were once 31%
wrong (commit history) and must not be duplicated. Like `Common`, it has no
`initialize` block (pure helpers), so it is a safe `lean_lib` root.
-/

namespace WorkerPlugins.ReverseElab

open Lean Lean.Meta Lean.Elab Lean.PrettyPrinter

/-- Outcome of reverse-elaborating one proof term. `method` records which rung
of the ladder won, so a consumer can judge decomposition quality honestly:
  * `structural`                      — `cases`/`have`/`by_cases` decomposition,
                                        recursing into branches (Tier-2)
  * `rfl` / `intro_rfl`               — proof was reflexivity (after intros)
  * `exact` / `intro_exact`           — small, legible body via `exact`
  * `exact_opaque` / `intro_exact_opaque`
      — verified, but the `exact`'d body is an automation blob (rw/simp/omega/
        decide residue): the intros are real decomposition, the body is not
  * `exact_whole`                     — verified, zero decomposition (one big
                                        `exact`, not even intros peeled)
  * `fail`                            — nothing verified; `script` is empty
The `_opaque`/`_whole`/`fail` labels exist specifically so a quality metric does
not count an opaque blob as a genuine decomposition. -/
structure ScriptResult where
  script : String
  method : String
  deriving Inhabited

/-- Delaborate with explicit args / universes / full names / proofs forced on,
maximizing the chance the printed term re-elaborates to the same thing. Verbose
but round-trip-safe; used as the fallback delaboration. -/
def delabExplicit (e : Expr) : MetaM Term :=
  withOptions (fun o =>
    let o := pp.explicit.set o true
    let o := pp.universes.set o true
    let o := pp.fullNames.set o true
    pp.proofs.set o true) do
    delab e

/-- Number of DISTINCT sub-expressions of `e` (sharing-aware: a subterm reachable
by many paths is counted once). O(actual term size), unlike `sizeWithoutSharing`
which re-counts shared nodes and can blow up on the heavily-shared proof terms we
see here. This is the cost proxy used to pre-filter pathological proofs before
reverse-elaboration (see `reverseProofGuarded`): the wall-time of re-elaborating
and `isDefEq`-checking a candidate scales with the real (shared) term size, which
`approxDepth` (capped, depth-only) does not capture. -/
partial def distinctNodes (e : Expr) : Nat :=
  go e {} |>.size
where
  go (e : Expr) (seen : Std.HashSet Expr) : Std.HashSet Expr :=
    if seen.contains e then seen
    else
      let seen := seen.insert e
      match e with
      | .app f a         => go a (go f seen)
      | .lam _ d b _     => go b (go d seen)
      | .forallE _ d b _ => go b (go d seen)
      | .letE _ t v b _  => go b (go v (go t seen))
      | .mdata _ e       => go e seen
      | .proj _ _ e      => go e seen
      | _                => seen

/-- Heuristic threshold on `Expr.approxDepth`: bodies shallower than this are
treated as a genuine, human-legible `exact` target; deeper ones are flagged as
automation residue (rw/simp/omega/decide blobs) so the `method` label stays
honest about how much real decomposition happened. -/
def atomicDepthThreshold : UInt32 := 8

/-- True when `e` is shallow enough to count as an honestly-decomposed `exact`
target rather than an opaque automation blob. -/
def isAtomicBody (e : Expr) : Bool :=
  e.approxDepth < atomicDepthThreshold

/-- True when `e`'s head is a reflexivity proof (`Eq.refl`/`Iff.refl`/`rfl`/
`HEq.refl`), i.e. a candidate for the `rfl` tactic. -/
def isReflHeaded (e : Expr) : Bool :=
  let e := e.cleanupAnnotations
  e.isAppOf ``Eq.refl || e.isAppOf ``Iff.refl || e.isAppOf ``rfl
    || e.isAppOf ``HEq.refl || e.isAppOf ``Iff.rfl

/-- Render a tactic sequence as a `by …` block string. -/
def renderBy (seq : TSyntax ``Lean.Parser.Tactic.tacticSeq) : MetaM String := do
  let byTerm ← `(by $seq)
  return (← ppTerm byTerm).pretty 100

/-- Per-attempt heartbeat budget for verification. Each `tryElab` resets the
heartbeat baseline (`withCurrHeartbeats`) and runs under this cap so a single
pathological candidate (re-elaborating a giant omega/simp blob) can time out
*locally* and fall back, without consuming the global extraction budget or
aborting the run. In raw heartbeats (the option is ×1000); 400000 ≈ twice the
default 200k-heartbeat ceiling, generous enough for honest proofs. -/
def verifyHeartbeats : Nat := 4000000

/-- Tight heartbeat budget for a *closer* attempt (`simp`/`omega`/`aesop`/…).
Closers are guesses tried in bulk (the menu × every opaque proof), so they must
fail fast: a closer that cannot shut the goal within this budget is treated as
"doesn't apply" rather than allowed to burn the full `verifyHeartbeats`. Much
smaller than `verifyHeartbeats` to keep whole-corpus extraction tractable. -/
def closerHeartbeats : Nat := 400000

/-- Overall per-theorem heartbeat budget for the WHOLE reverse-elaboration of one
proof (all candidate construction + verification combined). A secondary bound:
the PRIMARY guard is now the per-theorem WALL-CLOCK deadline applied by the
caller (`CorpusManifest.reverseProofGuarded`), because heartbeats track *work*
and not *wall time* — on the worker path a single `isDefEq` on a giant freshly-
elaborated term can run for many seconds while accruing few heartbeats, so a
heartbeat cap alone cannot bound latency (measured: an earlier 12M budget let
files run minutes and ride the request timeout; even 1M still lost 3 files).

It must be GENEROUS, because a success is not necessarily cheap: a late-winning
method (e.g. `intro_exact_opaque`) only verifies after the higher-priority
structural/rfl/exact candidates ahead of it have each been constructed and
failed, so its CUMULATIVE cost is what matters. Import-path data: the most
expensive genuine results reached ~10.5M (`structural`) and ~7.8M
(`intro_exact_opaque`) heartbeats total; capping below that turns real
decompositions into false fails. 12M clears the worst observed success.

Crucially this does NOT make normal fails slow: a fail "fails" by trying its ~9
candidates and having none verify, which costs their natural total (~2.4M median
on the import path) — nowhere near 12M. Only a GIANT-term proof approaches the
ceiling, and those accrue heartbeats slowly relative to wall time, so they are
bounded by the caller's wall-clock guard (`reverseProofGuarded`) long before this
heartbeat ceiling would bite. Re-measure if recognizers/corpus change. -/
def reverseHeartbeats : Nat := 12000000

/-- Per-step heartbeat budget for candidate *construction* (delaboration +
structural recursion). A secondary per-step valve under `reverseHeartbeats`:
`buildCandidates` calls `delab`/`delabExplicit`/`buildStructured`, and although
the delaborator polls `checkSystem` per node (so it is not truly unbounded), a
giant `omega`/`simp`/`decide` certificate delaborated with `pp.proofs`/
`pp.explicit` on can still be costly. Each construction step is charged against
the REMAINING per-theorem budget (see `reverseProof`), so once the theorem's
overall budget is spent further construction fails fast and the candidate is
skipped — exactly as `observing?` already degrades a delaboration error. -/
def constructHeartbeats : Nat := 4000000

/-- Run a candidate-construction step under a FRESH heartbeat baseline and a
bounded per-step cap, returning `none` on any failure — ordinary delaboration
error, heartbeat/recursion blowup on a pathological term, everything but a
genuine interrupt (which is re-raised so extraction stays cancellable). A strict
upgrade of `observing?`: in `CoreM` a plain `observing?`/`try` auto-rethrows
*runtime* exceptions (the heartbeat/recursion timeouts we specifically need to
absorb here), so `tryCatchRuntimeEx` is mandatory, not stylistic. State is fully
restored on every path.

`budget == 0` would mean UNLIMITED (Lean's `checkMaxHeartbeatsCore` early-returns
on a 0 cap), the opposite of intent, so callers pass `Nat.max 1 …`. -/
def boundedConstruct {α} (act : MetaM α) (budget : Nat := constructHeartbeats) :
    MetaM (Option α) :=
  withoutModifyingState <|
  withCurrHeartbeats <|
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget }) <|
  tryCatchRuntimeEx (some <$> act) (fun _ => pure none)

/-- Heartbeats still available in the per-theorem budget, measured from `hbStart`
(the global `IO.getNumHeartbeats` reading captured at the top of `reverseProof`).

Crucial detail: the per-step wrappers (`boundedConstruct`/`tryElab`/
`verifyRendered`) each call `withCurrHeartbeats`, which RESETS the per-step
baseline — so a single outer `maxHeartbeats` would be silently defeated by those
resets. The global `IO.getNumHeartbeats` counter is NOT reset by them, so
measuring `now - hbStart` against it yields true cumulative spend across all
construction and verification done so far. Clamped to ≥1 because a `0` cap is
Lean's "unlimited" sentinel — the opposite of an exhausted budget. -/
def budgetRemaining (hbStart : Nat) (overall : Nat := reverseHeartbeats) : MetaM Nat := do
  let spent := (← IO.getNumHeartbeats) - hbStart
  return if spent ≥ overall then 1 else Nat.max 1 (overall - spent)

/-- Re-elaborate a candidate tactic sequence against a fresh goal of type `ty`,
read back the synthesized proof, and `isDefEq`-check it against the original
term `v`. Pure verification: state is fully restored on every path (success,
goal-left-open, or thrown error), so the surrounding environment walk is never
perturbed. Interrupts are re-raised so extraction stays cancellable; every
other failure (elaboration error, heartbeat/recursion blowup on a pathological
candidate) degrades to `false` so we fall back rather than abort.

The attempt runs with a fresh heartbeat baseline and a bounded per-attempt cap
so verification cost is charged locally, not against the whole-run budget. -/
def tryElab (ty v : Expr) (seq : Syntax) (budget : Nat := verifyHeartbeats) : MetaM Bool :=
  withoutModifyingState <|
  withCurrHeartbeats <|
  withTheReader Core.Context (fun ctx => { ctx with maxHeartbeats := budget }) <|
  -- `tryCatchRuntimeEx` (NOT a plain `try`/`catch`): ordinary `MonadExcept`
  -- catch in CoreM auto-rethrows *runtime* exceptions (heartbeat / recursion
  -- timeouts), so a bare `catch` would let a local verify timeout escape and
  -- abort the whole extraction. `tryCatchRuntimeEx` catches those too, while
  -- still re-raising genuine interrupts — exactly the fall-back-don't-abort
  -- behavior we want for a single pathological candidate.
  tryCatchRuntimeEx
    (do
      let goal ← mkFreshExprMVar (some ty)
      let (remaining, _) ← Lean.Elab.runTactic goal.mvarId! seq
      if !remaining.isEmpty then
        return false
      let v' ← instantiateMVars goal
      -- Soundness: a Prop goal is proof-irrelevant, so `isDefEq v v'` is
      -- VACUOUSLY true for any `v'` of type `ty` — including a `sorryAx`-filled
      -- term from a partially-failed tactic. We must reject `sorry` explicitly,
      -- or a script that only half-closes the goal would be accepted. The
      -- `remaining.isEmpty` check above guards open goals; this guards
      -- error-recovery sorries that close the goal with `sorryAx`.
      if v'.hasSorry then return false
      withNewMCtxDepth (isDefEq v v'))
    (fun _ => pure false)

/-- Sanitize a binder name for use in an `intro`. Hygienic / inaccessible
names (those Lean renders with a `✝` dagger, plus the anonymous name) don't
round-trip as source identifiers, so we replace them with a fresh readable
`x{idx}`. Ordinary user names pass through unchanged. -/
def sanitizeBinder (n : Name) (idx : Nat) : Name :=
  let bad := n.isAnonymous || n.hasMacroScopes || (toString n).contains '✝'
  if bad then Name.mkSimple s!"x{idx}" else n

/-- Peel leading lambda binders (seeing through `mdata`), introducing a real
local for each so the body can be delaborated in scope. Binder names are
sanitized (see `sanitizeBinder`); the local is declared under the sanitized
name so the delaborated body refers to it by that name. Hands the collected
sanitized names and the in-context body to `k`. -/
partial def peelLambdas {α} (v : Expr) (acc : Array Name)
    (k : Array Name → Expr → MetaM α) : MetaM α := do
  match v.consumeMData with
  | .lam n d b _ =>
      let n := sanitizeBinder n acc.size
      withLocalDeclD n d fun x =>
        peelLambdas (b.instantiate1 x) (acc.push n) k
  | body => k acc body

/-! ### Tier-2: structural recognizers (`cases`)

The dominant shape among proofs that Tier-1 cannot decompose is `T.casesOn`
applied to a dependent motive — a single huge term that does not round-trip,
but whose individual branches do (after `cases`, the goal's motive is
re-synthesized per constructor, so each branch's proof is a smaller,
motive-free subterm). We recurse into the branches and emit a `cases … with`
script; the whole script is still verified by `tryElab`, so a misfire just
falls back to the Tier-1 ladder. -/

/-- Maximum `cases` nesting depth, to bound recursion / output size. -/
def structMaxDepth : Nat := 6

/-- Standard goal-closing tactics to try, in rough order of corpus likelihood,
when a body is opaque automation residue. By proof irrelevance any of these that
closes the goal yields an equally-valid proof — so when the original proof was
produced by e.g. `omega`, re-running `omega` recovers the author's actual
tactic, which is far more useful than a 500-char `exact <blob>`. The emitted
`method` is `intro_<name>` so consumers can see which closer won. Each candidate
is still verified (sound: rejects `sorry`/open goals), so a closer that does not
actually prove the goal is simply skipped. -/
def closerTactics : Array (String × String) := #[
  ("rfl",       "rfl"),
  ("simp",      "simp"),
  ("omega",     "omega"),
  ("decide",    "decide"),
  ("assumption","assumption"),
  ("trivial",   "trivial"),
  ("simp_all",  "simp_all")
]

/-- Allocate a re-parseable binder name. Good user names pass through; bad ones
(anonymous, macro-scoped, dagger-`✝`) become a fresh `x{n}` keyed off the local
context size, which is monotone under nested `withLocalDecl` so names don't
collide across branch scopes. -/
def freshBinder (n : Name) : MetaM Name := do
  let bad := n.isAnonymous || n.hasMacroScopes || (toString n).contains '✝'
  if !bad then return n
  return Name.mkSimple s!"x{(← getLCtx).decls.size}"

/-- Peel all leading `@id _ payload` wrappers (and `mdata`). Elaborated proofs
are frequently wrapped in nested `id`s that carry no proof content. -/
partial def peelIdAll (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOf ``id && e.getAppNumArgs == 2 then peelIdAll e.appArg!
  else e

/-- Recognize a `letFun`-encoded `have`: the constant `letFun` applied as
`@letFun α β v (fun x : α => b)` (the elaboration of `have x : α := v; b`).
Returns `(binderName, binderType, value, body)`. `Lean.Expr.letFun?` existed in
older Lean but was removed; we destructure the application directly. -/
def letFun? (e : Expr) : Option (Name × Expr × Expr × Expr) :=
  match e.consumeMData.getAppFnArgs with
  | (``letFun, #[α, _β, v, f]) =>
      match f.consumeMData with
      | .lam n _ b _ => some (n, α, v, b)
      | _            => none
  | _ => none

/-- `Nat.recAux`/`Nat.casesAuxOn` (and similar `@[induction_eliminator]`
abbrevs) are `defnInfo`, not recursors, so `isRecCore`/`isCasesOnRecursor`
reject them — but they delta-unfold to the real `T.rec`/`T.casesOn` with the
same argument structure. If `e`'s head name ends in `recAux`/`casesAuxOn`,
unfold one step to expose the underlying eliminator; otherwise return `e`. -/
def unfoldAuxEliminator (e : Expr) : MetaM Expr := do
  let .const name _ := e.getAppFn | return e
  let s := name.getString!
  if s == "recAux" || s == "casesAuxOn" then
    match ← Meta.unfoldDefinition? e with
    | some e' => return e'
    | none    => return e
  return e

/-- Recognize a `T.casesOn` application. Returns the discriminant (major
premise) and, per constructor in declaration order, its short name, field
count, and minor-premise expression. `none` if `e` is not a (fully applied)
casesOn. casesOn argument layout: params, motive, indices, **major**, minors. -/
def recognizeCasesOn (e : Expr) :
    MetaM (Option (Expr × Array (Name × Nat × Expr))) := do
  let e ← unfoldAuxEliminator e.consumeMData
  let .const name _ := e.getAppFn | return none
  unless isCasesOnRecursor (← getEnv) name do return none
  let some ival ← (do
      try pure (some (← getConstInfoInduct name.getPrefix))
      catch _ => pure none) | return none
  let args := e.getAppArgs
  let majorIdx := ival.numParams + 1 + ival.numIndices
  let firstMinor := majorIdx + 1
  let ctors := ival.ctors.toArray
  if args.size < firstMinor + ctors.size then return none
  let major := args[majorIdx]!
  let mut branches : Array (Name × Nat × Expr) := #[]
  for h : i in [0:ctors.size] do
    let ctor := ctors[i]
    let minor := args[firstMinor + i]!
    -- Pattern binds exactly the constructor's fields (`numFields`). Any further
    -- lambdas in the minor are hypotheses `cases` reverted over the
    -- discriminant; tactic-mode `cases` re-introduces those automatically into
    -- the branch context, so they are NOT named in the `| ctor … =>` pattern —
    -- the branch body's own `intro` spine (via `buildStructured`) handles them.
    let some cval ← (do
        try pure (some (← getConstInfoCtor ctor))
        catch _ => pure none) | return none
    branches := branches.push
      (Name.mkSimple ctor.getString!, cval.numFields, minor)
  return some (major, branches)

/-- Peel exactly `n` (or fewer, if the term runs out) leading lambdas with
fresh binder names, then hand the binder names and remaining body to `k`. Used
to split a casesOn minor premise into its constructor-field binders and the
branch body. -/
partial def peelLambdasN {α} (e : Expr) (n : Nat) (acc : Array Name)
    (k : Array Name → Expr → MetaM α) : MetaM α := do
  if n == 0 then k acc e
  else match e.consumeMData with
    | .lam nm d b _ =>
        let nm ← freshBinder nm
        withLocalDeclD nm d fun x => peelLambdasN (b.instantiate1 x) (n-1) (acc.push nm) k
    | body => k acc body

/-- Recognize a genuine recursor application `T.rec` (a `RecursorVal`, NOT a
casesOn aux). Returns the major premise and, per minor premise in rule order,
its constructor short name, the number of leading binders it takes (constructor
fields **plus** induction hypotheses, from `RecursorRule.nfields` + IH count),
and the minor expression. `none` if `e` is not a fully-applied recursor.

Recursor argument layout (differs from casesOn — the major is LAST):
params, motives, **minors**, indices, major. We only handle the common
single-motive, no-index (or indices we can delaborate) shape; anything we can't
slice cleanly returns `none` and the caller falls back. -/
def recognizeRec (e : Expr) :
    MetaM (Option (Expr × Array (Name × Nat × Expr))) := do
  let e ← unfoldAuxEliminator e.consumeMData
  let .const name _ := e.getAppFn | return none
  unless isRecCore (← getEnv) name do return none
  let some (.recInfo rval) := (← getEnv).find? name | return none
  -- Only single-motive recursors (ordinary inductive elimination).
  unless rval.numMotives == 1 do return none
  let args := e.getAppArgs
  if args.size < rval.getMajorIdx + 1 then return none
  let major := args[rval.getMajorIdx]!
  let firstMinor := rval.getFirstMinorIdx
  let rules := rval.rules.toArray
  if rules.size != rval.numMinors then return none
  let mut branches : Array (Name × Nat × Expr) := #[]
  for h : i in [0:rules.size] do
    let rule := rules[i]
    let minor := args[firstMinor + i]!
    -- Binders to peel for this minor = fields + IHs. We don't know the IH count
    -- from `nfields` alone, so peel ALL leading lambdas of the minor; that is
    -- exactly the `induction … with | ctor a ih => …` binder list.
    let nbind ← lambdaTelescope minor fun xs _ => pure xs.size
    branches := branches.push
      (Name.mkSimple rule.ctor.getString!, nbind, minor)
  return some (major, branches)

/-- Parse a tactic string to `Syntax`; `none` if it does not parse. -/
private def parseTactic? (tac : String) : MetaM (Option (TSyntax `tactic)) :=
  observing? (do
    let parsed ← ofExcept (Lean.Parser.runParserCategory (← getEnv) `tactic tac)
    pure (⟨parsed⟩ : TSyntax `tactic))

/-- Does running `closerStx` alone close a fresh goal of type `goalTy` — no
remaining goals, no `sorry`? State-isolated and `closerHeartbeats`-bounded.
Sound by the `remaining.isEmpty` + `hasSorry` guards (proof irrelevance otherwise
makes any term of the right type vacuously accepted). -/
private def closerClosesGoal (goalTy : Expr) (closerStx : TSyntax `tactic) : MetaM Bool :=
  withoutModifyingState <| withCurrHeartbeats <|
  withTheReader Core.Context (fun c => { c with maxHeartbeats := closerHeartbeats }) <|
  tryCatchRuntimeEx
    (do
      let goal ← mkFreshExprMVar (some goalTy)
      let seq ← `(tacticSeq| $[$(#[closerStx])]*)
      let (remaining, _) ← Lean.Elab.runTactic goal.mvarId! seq
      if !remaining.isEmpty then return false
      if (← instantiateMVars goal).hasSorry then return false
      return true)
    (fun _ => pure false)

/-- At a structural LEAF (proof term `e`, in the current local context), try each
candidate closer against the leaf's goal (`inferType e`) and return the first that
closes it. Candidates are the no-arg `closerTactics` menu PLUS `extraClosers` —
argument-bearing tactics harvested verbatim from the author's source proof (e.g.
`simp [Array.length_toList]`), an INFORMED guess that may close a goal no-arg
`simp` cannot. Each is still verified, so a guess that does not reproduce the
proof is dropped; and the whole assembled script is re-verified by
`verifyRendered`, so a leaf closer that does not compose globally falls back. -/
def tryLeafCloser (extraClosers : Array String) (e : Expr) :
    MetaM (Option (TSyntax `tactic)) := do
  let goalTy ← inferType e
  -- Author-sourced args first: a `simp [lemmas]` that fires is more specific (and
  -- more useful as training signal) than bare `simp` stumbling onto the same goal.
  for tac in extraClosers ++ closerTactics.map (·.2) do
    let some closerStx ← parseTactic? tac | continue
    if (← closerClosesGoal goalTy closerStx) then
      return some closerStx
  return none

/-- Leaf-emission configuration threaded through the structural builder. Bundles
the closer on/off switch with the author-sourced `extraClosers` so the recursion
carries ONE value instead of two parallel parameters. `closers := false` ⇒ leaves
are always plain `exact <term>` (the safety-net structural variant). -/
structure LeafConfig where
  closers      : Bool
  extraClosers : Array String := #[]

/-- The argument-free leaf config (no source-harvested args). -/
def LeafConfig.noArgs (closers : Bool) : LeafConfig := { closers }

mutual
/-- Recursively build a structured tactic sequence for proof term `e` in the
current local context, using `delabFn` for leaf terms. Emits `intro` for the
lambda spine and `cases … with` for a `T.casesOn`, recursing into each branch;
bottoms out at a leaf (a no-arg closer when `enableClosers` and one fires, else
`exact`). NOT verified here — the caller verifies the whole assembled script and
falls back on any mismatch. `depth` bounds nesting. -/
partial def buildStructured (delabFn : Expr → MetaM Term) (cfg : LeafConfig)
    (depth : Nat) (e : Expr) :
    MetaM (TSyntax ``Lean.Parser.Tactic.tacticSeq) :=
  peelLambdas e #[] fun names body => do
    let introTacs ← names.mapM fun n => `(tactic| intro $(mkIdent n):ident)
    let bodyC := peelIdAll body
    let tail : Array (TSyntax `tactic) ← buildTail delabFn cfg depth bodyC
    `(tacticSeq| $[$(introTacs ++ tail)]*)

/-- Build the non-`intro` tail of a structured sequence for body `e` (already
`id`-peeled, in scope). Dispatches on the head: `letFun`/`letE` → `have` then
recurse; `dite` → `by_cases`; `casesOn` → `cases … with`; genuine `T.rec` →
`induction … with`; a constructor with proof fields → `refine ⟨…⟩` + `next`;
otherwise a LEAF — a no-arg closer if `enableClosers` and one closes the leaf
goal, else `exact <term>`. Each recurses into sub-proofs. -/
partial def buildTail (delabFn : Expr → MetaM Term) (cfg : LeafConfig)
    (depth : Nat) (e : Expr) :
    MetaM (Array (TSyntax `tactic)) := do
  if depth == 0 then return #[← leafTac delabFn cfg e]
  -- `have` for letFun / letE: name the intermediate, recurse into the body.
  match letFun? e with
  | some (n, ty, val, body) =>
      let nm ← freshBinder n
      let tyStx ← delabFn ty
      let valSeq ← buildStructured delabFn cfg (depth - 1) val
      withLocalDeclD nm ty fun x => do
        let rest ← buildTail delabFn cfg (depth - 1) (peelIdAll (body.instantiate1 x))
        let haveTac ← `(tactic| have $(mkIdent nm):ident : $tyStx:term := by $valSeq)
        return #[haveTac] ++ rest
  | none =>
    match e.consumeMData with
    | .letE n ty val body _ =>
        let nm ← freshBinder n
        let tyStx ← delabFn ty
        let valSeq ← buildStructured delabFn cfg (depth - 1) val
        withLocalDeclD nm ty fun x => do
          let rest ← buildTail delabFn cfg (depth - 1) (peelIdAll (body.instantiate1 x))
          let haveTac ← `(tactic| have $(mkIdent nm):ident : $tyStx:term := by $valSeq)
          return #[haveTac] ++ rest
    | _ =>
      -- `dite c (fun h => t) (fun h => e)` → `by_cases h : c`. The by_cases
      -- macro tags its two goals with hygienic names, so we address them
      -- positionally with `next => …` rather than `case pos/neg`, which avoids
      -- the dagger-name round-trip break. If anything is off, `verifyRendered`
      -- rejects the whole script and we fall back to the Tier-1 ladder.
      if e.isAppOf ``dite && e.getAppNumArgs == 5 then
        let args := e.getAppArgs
        let cStx ← delabFn args[1]!
        let hName ← peelLambdasN args[3]! 1 #[] fun ns _ => pure (ns.getD 0 `h)
        let posSeq ← peelLambdasN args[3]! 1 #[] fun _ t =>
          buildStructured delabFn cfg (depth - 1) (peelIdAll t)
        let negSeq ← peelLambdasN args[4]! 1 #[] fun _ t =>
          buildStructured delabFn cfg (depth - 1) (peelIdAll t)
        pure #[← `(tactic| by_cases $(mkIdent hName) : $cStx:term),
               ← `(tactic| next => $posSeq),
               ← `(tactic| next => $negSeq)]
      else if let some (major, branches) ← recognizeCasesOn e then
        let majorStx ← delabFn major
        let alts ← branches.mapM fun (ctor, nfields, minor) =>
          peelLambdasN minor nfields #[] fun fields bbody => do
            let branchSeq ← buildStructured delabFn cfg (depth - 1) bbody
            let fieldIds := fields.map mkIdent
            `(Lean.Parser.Tactic.inductionAlt|
                | $(mkIdent ctor):ident $fieldIds:ident* => $branchSeq)
        pure #[← `(tactic| cases $majorStx:term with $alts:inductionAlt*)]
      -- Genuine recursor `T.rec` → `induction major with | ctor binders => …`.
      else if let some (major, branches) ← recognizeRec e then
        let majorStx ← delabFn major
        let alts ← branches.mapM fun (ctor, nbind, minor) =>
          peelLambdasN minor nbind #[] fun binders bbody => do
            let branchSeq ← buildStructured delabFn cfg (depth - 1) bbody
            let binderIds := binders.map mkIdent
            `(Lean.Parser.Tactic.inductionAlt|
                | $(mkIdent ctor):ident $binderIds:ident* => $branchSeq)
        pure #[← `(tactic| induction $majorStx:term with $alts:inductionAlt*)]
      -- Constructor application `C params… fields…` → `refine ⟨holes⟩` where
      -- proof fields become `?_` goals recursed via `next`, data fields are
      -- delaborated inline. Only when there is ≥1 proof field to decompose.
      else if let some tacs ← recognizeCtor delabFn cfg depth e then
        pure tacs
      else pure #[← leafTac delabFn cfg e]

/-- The tactic emitted at a structural leaf: when `cfg.closers`, a closer (no-arg
menu + author-sourced `cfg.extraClosers`) that closes the leaf goal — the
canonical, argument-bounded choice — else `exact <delaborated term>`. The `exact`
keeps the decomposition verified even when no closer applies; whether it counts
toward a fixed-vocabulary training target is a consumer concern (the `method`
label distinguishes the cases). -/
partial def leafTac (delabFn : Expr → MetaM Term) (cfg : LeafConfig) (e : Expr) :
    MetaM (TSyntax `tactic) := do
  if cfg.closers then
    if let some closerStx ← tryLeafCloser cfg.extraClosers e then
      return closerStx
  `(tactic| exact $(← delabFn e))

/-- Constructor recognizer. If `e` is an application of a structure/inductive
constructor with at least one proof-typed field, emit `refine ⟨…⟩` with a `?_`
hole for each proof field (recursed via `next => …`) and the delaborated term
for each data field. Returns `none` when `e` is not a constructor app or has no
proof field worth decomposing (so the caller keeps the leaf `exact`). -/
partial def recognizeCtor (delabFn : Expr → MetaM Term) (cfg : LeafConfig)
    (depth : Nat) (e : Expr) :
    MetaM (Option (Array (TSyntax `tactic))) := do
  let .const cname _ := e.getAppFn | return none
  let some (.ctorInfo cval) := (← getEnv).find? cname | return none
  let args := e.getAppArgs
  if args.size != cval.numParams + cval.numFields then return none
  if cval.numFields == 0 then return none
  let fields := args[cval.numParams : args.size].toArray
  -- Classify each field: proof → `?_` (recurse), data → delaborated term.
  let mut elems : Array Term := #[]
  let mut proofFields : Array Expr := #[]
  for f in fields do
    if (← Meta.isProof f) then
      proofFields := proofFields.push f
      elems := elems.push (← `(?_))
    else
      elems := elems.push (← delabFn f)
  if proofFields.isEmpty then return none
  let refineTac ← `(tactic| refine ⟨$elems,*⟩)
  -- One `next => <seq>` per proof field, in order, matching the `?_` goals.
  let mut nexts : Array (TSyntax `tactic) := #[]
  for pf in proofFields do
    let seq ← buildStructured delabFn cfg (depth - 1) (peelIdAll pf)
    nexts := nexts.push (← `(tactic| next => $seq))
  return some (#[refineTac] ++ nexts)
end

/-- Whether the top of `v` (after the intro spine and `id` peeling) is a shape
the structural builder decomposes — a `casesOn`, a `letFun`, or a `letE`.
Avoids emitting a structural candidate that would just duplicate the Tier-1
`exact`. -/
def topIsStructural (v : Expr) : MetaM Bool :=
  peelLambdas v #[] fun _ body => do
    let b := peelIdAll body
    if (letFun? b).isSome then return true
    if b.consumeMData.isLet then return true
    if b.isAppOf ``dite && b.getAppNumArgs == 5 then return true
    if (← recognizeCasesOn b).isSome then return true
    if (← recognizeRec b).isSome then return true
    -- ctor-headed with a proof field: a `refine ⟨…⟩` candidate.
    if let .const cname _ := b.getAppFn then
      if let some (.ctorInfo cval) := (← getEnv).find? cname then
        if cval.numFields > 0 && b.getAppArgs.size == cval.numParams + cval.numFields then
          return true
    return false

/-- Build candidate tactic sequences (pure syntax) in priority order: most
decomposed / most readable first, whole-term `exact` last. Delaboration happens
here, inside the peeled local context, so body fvars are in scope. Verification
happens *after* this returns, in the clean top-level context.

Each construction step is capped at `min constructHeartbeats (budget left from
hbStart)` so the cumulative per-theorem budget (`reverseHeartbeats`) covers
construction as well as verification — a pathological term that eats the budget
in delaboration leaves nothing for later candidates, and they fail fast. -/
private def buildCandidates (v : Expr) (enableClosers : Bool) (extraClosers : Array String)
    (hbStart : Nat) :
    MetaM (Array (TSyntax ``Lean.Parser.Tactic.tacticSeq × String)) :=
  peelLambdas v #[] fun names body => do
    let nIntros := names.size
    let introTacs ← names.mapM fun n => `(tactic| intro $(mkIdent n):ident)
    let introLabel (s : String) : String := if nIntros > 0 then s!"intro_{s}" else s
    -- Closer configs for the structural builder: with args (preferred) and the
    -- plain-`exact` safety net. `noArgs false` ⇒ leaves are always `exact`.
    let cfgArgs : LeafConfig := { closers := true, extraClosers }
    let cfgPlain : LeafConfig := LeafConfig.noArgs false
    -- The `exact` of the body is honest about whether the body is a small
    -- human-legible term or an opaque automation blob (rw/simp/omega/decide).
    let exactKind := if isAtomicBody body then "exact" else "exact_opaque"
    -- Per-step construction cap: the smaller of the fixed per-step valve and
    -- whatever remains of the theorem's overall budget.
    let cBudget : MetaM Nat := return Nat.min constructHeartbeats (← budgetRemaining hbStart)
    let mut out : Array (TSyntax ``Lean.Parser.Tactic.tacticSeq × String) := #[]
    -- 0. Tier-2 structural candidate: intro spine + `cases … with` recursing
    -- into branches. Highest priority (most decomposed); only built when the
    -- body is actually a casesOn so we don't duplicate the Tier-1 exact.
    --
    -- With `--closers` we emit TWO structural variants per delaborator, in this
    -- order: leaf-CLOSER first (canonical, argument-free leaves — the goal), then
    -- the same decomposition with plain `exact <term>` leaves as a SAFETY NET.
    -- This matters because a leaf closer is verified only against its leaf goal
    -- in isolation; it may not compose in the assembled `cases`/`induction`
    -- branch (where the tactic-mode goal differs from the term's leaf type), in
    -- which case the closer variant fails whole-script `verifyRendered`. Without
    -- the plain-`exact` fallback that failure would sink the whole structural
    -- decomposition to `*_opaque`/`fail` — a regression vs. no closers. Emitting
    -- both lets the ranking keep the closer script when it holds and fall back to
    -- the working `exact` decomposition when it doesn't.
    if ← topIsStructural v then
      for delabFn in #[delab, delabExplicit] do
        if enableClosers then
          if let some seq ← boundedConstruct (buildStructured delabFn cfgArgs structMaxDepth v) (← cBudget) then
            out := out.push (seq, "structural")
        if let some seq ← boundedConstruct (buildStructured delabFn cfgPlain structMaxDepth v) (← cBudget) then
          out := out.push (seq, "structural")
    -- 1. intro …; rfl  (only when the body is reflexivity-headed)
    if isReflHeaded body then
      let seq ← `(tacticSeq| $[$(introTacs.push (← `(tactic| rfl)))]*)
      out := out.push (seq, introLabel "rfl")
    -- 2. ATOMIC body only: intro …; exact <small readable term>. A legible
    -- term beats guessing a closer, so it ranks above the closers.
    if isAtomicBody body then
      if let some t ← boundedConstruct (delab body) (← cBudget) then
        out := out.push (← `(tacticSeq| $[$(introTacs.push (← `(tactic| exact $t)))]*),
                         introLabel "exact")
      if let some t ← boundedConstruct (delabExplicit body) (← cBudget) then
        out := out.push (← `(tacticSeq| $[$(introTacs.push (← `(tactic| exact $t)))]*),
                         introLabel "exact")
    -- 3. Closer-guessing (opt-in via `--closers`): intro …; <closer>. By proof
    -- irrelevance any closer that shuts the goal is a valid proof, and recovers
    -- the high-level tactic the author likely used (omega/simp/…) instead of a
    -- giant `exact` blob. Ranked above the opaque exact so a one-liner wins;
    -- each is still verified. The author-sourced `extraClosers` (verbatim
    -- `simp [lemmas]` from the proof) are tried FIRST and labelled distinctly
    -- (`simp_args`) so a more-specific informed guess beats bare `simp`, and so
    -- the contribution of source-harvested args is measurable in `proof_method`.
    if enableClosers then
      let menu : Array (String × String) :=
        extraClosers.map (fun s => ("simp_args", s)) ++ closerTactics
      for (cname, ctac) in menu do
        if let some closerStx ← observing? (do
            let parsed ← ofExcept (Lean.Parser.runParserCategory (← getEnv) `tactic ctac)
            pure (⟨parsed⟩ : TSyntax `tactic)) then
          let seq ← `(tacticSeq| $[$(introTacs.push closerStx)]*)
          out := out.push (seq, introLabel cname)
    -- 4. OPAQUE body: intro …; exact <automation blob>. Verified fallback when
    -- no closer reproduces the proof; preserves the term but is unreadable.
    if !isAtomicBody body then
      if let some t ← boundedConstruct (delab body) (← cBudget) then
        out := out.push (← `(tacticSeq| $[$(introTacs.push (← `(tactic| exact $t)))]*),
                         introLabel exactKind)
      if let some t ← boundedConstruct (delabExplicit body) (← cBudget) then
        out := out.push (← `(tacticSeq| $[$(introTacs.push (← `(tactic| exact $t)))]*),
                         introLabel exactKind)
    -- 5. whole-term exact, no intro (readable then explicit). Closed `v`.
    if let some t ← boundedConstruct (delab v) (← cBudget) then
      let seq ← `(tacticSeq| $[$(#[← `(tactic| exact $t)])]*)
      out := out.push (seq, "exact_whole")
    if let some t ← boundedConstruct (delabExplicit v) (← cBudget) then
      let seq ← `(tacticSeq| $[$(#[← `(tactic| exact $t)])]*)
      out := out.push (seq, "exact_whole")
    return out

/-- Re-parse a rendered `by …` script STRING and verify it elaborates to a term
defeq to `v`. This checks the artifact we actually store — not just the
in-memory `Syntax` — closing the gap where a candidate can pass `tryElab` (via
`runTactic`, which is more permissive about e.g. hygienic `case` tags) yet fail
when the printed string is re-parsed. State-isolated and timeout-bounded like
`tryElab`.

Sound on its own: `errToSorry := false` makes a failed elaboration THROW (so we
catch and reject) instead of silently becoming `sorry`, and `hasSorry` rejects
any residual `sorryAx`. Without this, proof irrelevance would make `isDefEq v e`
accept a `sorry` proof of the right Prop. -/
def verifyRendered (ty v : Expr) (script : String)
    (budget : Nat := verifyHeartbeats) : MetaM Bool := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `term script with
  | .error _ => return false
  | .ok stx =>
    withoutModifyingState <| withCurrHeartbeats <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := budget }) <|
    tryCatchRuntimeEx
      (do
        let e ← Lean.Elab.Term.TermElabM.run' (ctx := {}) <|
          withReader (fun c => { c with errToSorry := false }) do
            let e ← Term.elabTerm stx (some ty)
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e
        if e.hasSorry then return false
        withNewMCtxDepth (isDefEq v e))
      (fun _ => pure false)

/-- Reverse-elaborate the proof term `v : ty` into a verified tactic script.
Tries each candidate in priority order and returns the first whose rendered
string re-parses and reproduces `v` up to definitional equality; if none do,
returns `method := "fail"`.

Two-stage verification: the cheap in-memory `tryElab` filters candidates, then
`verifyRendered` confirms the STORED STRING is itself a valid proof. A candidate
that passes the first but fails the second (e.g. a script using inaccessible
hygienic names that don't round-trip through the printer) is correctly
rejected, so we never emit a string that isn't a real proof. -/
def reverseProof (ty v : Expr) (enableClosers : Bool := false)
    (extraClosers : Array String := #[]) : MetaM ScriptResult := do
  -- Closer candidates (`intro_simp`, `simp`, …) are bulk guesses, so verify
  -- them under the tight `closerHeartbeats` budget — a closer that needs the
  -- full budget to fire is not the intended fast proof, and letting every
  -- closer burn `verifyHeartbeats` makes whole-corpus extraction intractable.
  -- `simp_args` (author-sourced `simp [lemmas]`) are closers too for budgeting.
  let closerNames : Std.HashSet String :=
    (Std.HashSet.emptyWithCapacity : Std.HashSet String).insertMany
      ((closerTactics.map (·.1)).push "simp_args")
  -- Capture the global heartbeat counter ONCE up front. Every per-step cap below
  -- is computed as "what's left of `reverseHeartbeats` since here", so the whole
  -- reverse-elaboration of this proof — all construction + all verification — is
  -- bounded in aggregate. Without this a `fail` theorem runs every one of ~9
  -- candidates to its own per-attempt cap (tens of millions of heartbeats); the
  -- aggregate ceiling is what makes a hard proof fail in bounded time.
  let hbStart ← IO.getNumHeartbeats
  let candidates ← buildCandidates v enableClosers extraClosers hbStart
  for (seq, label) in candidates do
    -- Stop as soon as the per-theorem budget is spent: remaining candidates are
    -- lower-priority fallbacks, and a `fail` proof has nothing left worth trying.
    let remaining ← budgetRemaining hbStart
    if remaining ≤ 1 then break
    let isCloser :=
      closerNames.contains label ||
      (label.startsWith "intro_" && closerNames.contains (label.drop 6).toString)
    -- Per-attempt cap = the usual per-step valve, but never more than the budget
    -- still available to this theorem.
    let stepCap := if isCloser then closerHeartbeats else verifyHeartbeats
    let budget := Nat.min stepCap remaining
    if (← tryElab ty v seq.raw budget) then
      let script ← renderBy seq
      if (← verifyRendered ty v script (Nat.min stepCap (← budgetRemaining hbStart))) then
        return { script, method := label }
  return { script := "", method := "fail" }

end WorkerPlugins.ReverseElab
