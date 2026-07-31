/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import Corpus.CollectCommon
import Corpus.Frontend
import Corpus.Records
import Corpus.SourceSyntax
import Corpus.Verify

/-!
Per-step proof-state extraction: one record per tactic-proved theorem, carrying
the nested tree of author-written tactics with the goal state before and after
each one.

# Why

The corpus has two whole-proof representations and no interior. `body` /
`decl_source` are source slices (`Corpus.SourceSyntax`); `proof_script` is a
mechanically reverse-elaborated string (`Corpus.ReverseElab`). Neither can express
*given this goal, the author applied this tactic, and the goal became that* —
which is the unit of data tactic-level proof learning needs.

# How

The substrate already exists: `Frontend.ElabResult.trees` carries every file's
`InfoTree`s, and `Corpus.GrindInProof` already demonstrates restoring a mid-proof
goal from a `TacticInfo` (`{ctx with mctx := ti.mctxBefore}.runMetaM`). This
module generalizes that from one tactic kind to every author-written tactic, and
records goals instead of re-running anything.

Walk with `InfoTree.visitM` rather than `foldInfo` (which `GrindInProof` uses):
`visitM` threads the merged `ContextInfo` down and hands each node its children,
which is what tree reconstruction needs; `foldInfo` flattens and would lose the
nesting. Each node returns a FOREST (`Array RawStep`), so a dropped node simply
returns its children's forest and reparenting falls out for free.

# The two rules that matter

1. **Snapshot discipline.** A goal is an `MVarId`, meaningful only relative to a
   `MetavarContext`. `TacticInfo` carries two (`mctxBefore`/`mctxAfter`), and
   `goalsBefore` MUST be rendered under `mctxBefore` and `goalsAfter` under
   `mctxAfter`. One snapshot for both silently mis-instantiates metavariables, so
   a target shows `?m` where a concrete term belongs (or vice versa). Hence one
   `ContextInfo.runMetaM` entry per direction per step.

2. **Node selection is by parser category**, read from the file's own
   environment (`Lean.Parser.getParserCategory?` → `ParserCategory.kinds`) for
   both `tactic` and `conv`. This is not a stylistic choice over a denylist: the
   raw tree also contains `tacticSeq`, `tacticSeq1Indented`, `null`, `by`,
   `byTactic`, `cdotTk`, `«;»`, `«<;>»`, `withAnnotateState`, `convSeq`, … and
   atoms report their own text as their kind. The category IS the definition of
   "a tactic a user can write", it comes from the environment the file elaborated
   in, and it therefore stays correct across Lean versions and picks up
   project-defined tactics for free.

   A useful consequence: macro expansions (`trivial` → `apply`, `rfl` → `eqRefl`,
   `try` → `first`) are either uncategorized or carry no canonical range, so they
   are dropped and the OUTERMOST author form survives with no special collapse
   rule. `ProofStatesTests` guards that with an explicit assertion.

Combinators (`all_goals`, `<;>`, `repeat`) re-invoke `evalTactic` on the SAME
syntax once per goal, producing N sibling nodes each with a single-goal
`goalsBefore` (documented at `Corpus.GrindInProof`'s `collectGrindSites`). Here
the unit of data is one tactic AS WRITTEN, so those siblings are merged and
`invocations` records N — the deliberate inverse of grind-in-proof, whose unit is
one verification condition per goal.
-/

namespace Corpus.ProofStates

open Lean Lean.Elab Lean.Meta
open Corpus.SourceSyntax

/-! ## Bounding

Rendering every goal at every step is the cost centre, so this follows the
bounding pattern the repo already settled on (`reverseNodeCeiling`,
`grindDeadlineMs`, `tryCatchRuntimeEx`): a size pre-filter that refuses work
before it starts, a wall-clock deadline that sheds the tail, and a per-theorem
exception guard so one pathological proof costs one record rather than a file. -/

/-- Step-count ceiling per theorem. Above it the record is emitted with no steps
and `outcome := "skipped_large"`, rather than rendering thousands of goals. The
count is known before any `ppExpr` runs, so this refuses the work up front — the
same argument `CorpusManifest.reverseNodeCeiling` makes for size pre-filters over
time budgets. -/
def stepCeiling : Nat := 400

/-! ## The raw tree

`RawStep` is the tree as read off the `InfoTree`, before goal rendering and
indexing. It is deliberately `Info`-free — it holds only ranges, kinds, and goal
ids — so every transform below is a pure function over plain data that
`ProofStatesTests` can exercise without constructing an `InfoTree`. -/

/-- A kept tactic node, pre-rendering. `goalsBefore`/`goalsAfter` are indices into
the record's goal table, already interned by the walk. -/
structure RawStep where
  kind        : Name
  elaborator  : Name
  /-- File-relative byte offsets, from the canonical source range. -/
  startByte   : Nat
  endByte     : Nat
  startLine   : Nat
  startCol    : Nat
  endLine     : Nat
  endCol      : Nat
  goalsBefore : Array Nat
  goalsAfter  : Array Nat
  invocations : Nat := 1
  children    : Array RawStep := #[]
  deriving Inhabited, Repr

/-- Append preserving order, dropping duplicates. Goal ids are interned, so
equality of ids is equality of rendered goal states. -/
private def unionIds (a b : Array Nat) : Array Nat :=
  b.foldl (fun acc x => if acc.contains x then acc else acc.push x) a

/-- Merge sibling steps that share a `(range, kind)`: the same author-written
tactic re-invoked by a combinator once per goal. Goals become the ordered unions,
children concatenate, and `invocations` counts the invocations.

Order is the first occurrence's, so the result is deterministic. An invocation
with an empty `goalsBefore` (what `repeat t` produces once the goals run out)
contributes nothing to the union, which is correct: the union means "every goal
this tactic actually ran on". -/
def mergeSiblings (steps : Array RawStep) : Array RawStep := Id.run do
  let mut out : Array RawStep := #[]
  for s in steps do
    let same := fun (t : RawStep) =>
      t.startByte == s.startByte && t.endByte == s.endByte && t.kind == s.kind
    match out.findIdx? same with
    | some i =>
      let t := out[i]!
      out := out.set! i { t with
        goalsBefore := unionIds t.goalsBefore s.goalsBefore
        goalsAfter  := unionIds t.goalsAfter s.goalsAfter
        invocations := t.invocations + s.invocations
        children    := t.children ++ s.children }
    | none => out := out.push s
  return out

/-- Merge duplicate siblings, then order what remains by source position,
recursively.

Merging BEFORE sorting is deliberate, and the order matters twice over:

  * `visitM` hands back siblings in ELABORATION order, which for a combinator is
    the order the tactic ran on its goals. Merging first therefore builds
    `goals_before`/`goals_after` in goal order — the meaningful order — instead of
    an order imposed by a sort that cannot distinguish the invocations anyway.
  * It also makes the sort total. `qsort` is not stable, so ties would be resolved
    arbitrarily; after merging, two distinct steps can no longer share
    `(startByte, endByte, kind)`, so those three keys are a total order and the
    result is deterministic. -/
partial def normalize (steps : Array RawStep) : Array RawStep :=
  let merged := mergeSiblings steps
  let sorted := merged.qsort fun a b =>
    if a.startByte != b.startByte then a.startByte < b.startByte
    else if a.endByte != b.endByte then a.endByte < b.endByte
    else a.kind.toString < b.kind.toString
  sorted.map fun s => { s with children := normalize s.children }

/-- Assign dense pre-order `index` and `depth`, turning `RawStep`s into
`ProofStep`s. `slice` supplies each step's verbatim source text. -/
partial def toProofSteps (slice : Nat → Nat → String) (depth : Nat) (next : Nat)
    (steps : Array RawStep) : Array ProofStep × Nat := Id.run do
  let mut out : Array ProofStep := #[]
  let mut counter := next
  for s in steps do
    let index := counter
    counter := counter + 1
    let (children, counter') := toProofSteps slice (depth + 1) counter s.children
    counter := counter'
    out := out.push {
      index, depth
      tactic      := slice s.startByte s.endByte
      tacticKind  := s.kind.toString
      elaborator  := s.elaborator.toString
      startLine   := s.startLine
      startCol    := s.startCol
      endLine     := s.endLine
      endCol      := s.endCol
      startByte   := s.startByte
      endByte     := s.endByte
      goalsBefore := s.goalsBefore
      goalsAfter  := s.goalsAfter
      invocations := s.invocations
      children }
  return (out, counter)

/-! ### Goal renumbering

`visitM` is bottom-up, so goals get interned deepest-first and the opening goal
ends up with the HIGHEST id — `initial_goals: [2]` on a three-goal proof. The ids
are correct but the numbering is an artifact of the traversal, not of the proof.

Renumbering by first reference in step pre-order fixes that: goal 0 is always the
state the proof opened in, and ids increase roughly as the proof progresses. It
also drops any goal the final tree no longer references, so the table cannot carry
orphans. -/

/-- Collect goal ids in order of first reference, walking steps pre-order and
`goals_before` before `goals_after` (the order the proof encounters them). -/
partial def referencedGoals (steps : Array ProofStep) : Array Nat :=
  let rec go (acc : Array Nat) (ss : Array ProofStep) : Array Nat :=
    ss.foldl (fun acc s =>
      let acc := (s.goalsBefore ++ s.goalsAfter).foldl
        (fun acc g => if acc.contains g then acc else acc.push g) acc
      go acc s.children) acc
  go #[] steps

/-- Rewrite every goal reference through `remap`, recursively. -/
partial def remapSteps (remap : Std.HashMap Nat Nat) (steps : Array ProofStep)
    : Array ProofStep :=
  steps.map fun s => { s with
    goalsBefore := s.goalsBefore.filterMap (remap[·]?)
    goalsAfter  := s.goalsAfter.filterMap (remap[·]?)
    children    := remapSteps remap s.children }

/-- Renumber the goal table into step pre-order. Returns the reordered table and
the rewritten steps; goals unreferenced by `steps` are dropped. -/
def renumberGoals (goals : Array ProofGoal) (steps : Array ProofStep)
    : Array ProofGoal × Array ProofStep := Id.run do
  let order := referencedGoals steps
  let mut remap : Std.HashMap Nat Nat := {}
  let mut out : Array ProofGoal := #[]
  for old in order do
    if let some g := goals[old]? then
      remap := remap.insert old out.size
      out := out.push { g with id := out.size }
  return (out, remapSteps remap steps)

/-- Total steps including nested children. -/
partial def countSteps (steps : Array ProofStep) : Nat :=
  steps.foldl (fun n s => n + 1 + countSteps s.children) 0

/-- Deepest `depth` present, or 0 for an empty tree. -/
partial def depthOf (steps : Array ProofStep) : Nat :=
  steps.foldl (fun d s => Nat.max d (Nat.max s.depth (depthOf s.children))) 0

/-- Sorted distinct tactic kinds across the whole tree. -/
partial def kindsOf (steps : Array ProofStep) : Array String :=
  let rec go (acc : Array String) (ss : Array ProofStep) : Array String :=
    ss.foldl (fun acc s =>
      let acc := if acc.contains s.tacticKind then acc else acc.push s.tacticKind
      go acc s.children) acc
  (go #[] steps).qsort (· < ·)

/-- The same `RawStep` count, before rendering — used by the size pre-filter. -/
partial def countRaw (steps : Array RawStep) : Nat :=
  steps.foldl (fun n s => n + 1 + countRaw s.children) 0

/-! ## Goal rendering

Mirrors `Meta.ppGoal` (`Lean/Meta/PPGoal.lean`): sanitize the local context's
names, install it with its local instances, skip aux and implementation-detail
declarations, `simpMacroScopes` each user name, and `instantiateMVars` every type.
Consecutive same-type declarations are grouped so `a b : Nat` renders as one
hypothesis entry, matching the infoview.

Note `LocalContext` has no `ForIn` instance, so this folds explicitly with a
`(hyps, pendingNames, pendingType)` accumulator — the shape `ppGoal` itself uses. -/

/-- Line width for goal pretty-printing, matching `CorpusManifest.ppExpr120`. -/
private def ppWidth : Nat := 120

private def ppAt (e : Expr) : MetaM String := do
  return ((← Meta.ppExpr e).pretty ppWidth).trimAsciiEnd.copy

/-- Render one goal's local context and target. `none` when the metavariable is
not in the ambient context (a stale or ill-formed node), which the caller skips. -/
def renderGoal (mvarId : MVarId) : MetaM (Option (Array ProofHyp × String × String)) := do
  let some mvarDecl := (← getMCtx).findDecl? mvarId | return none
  let lctx := mvarDecl.lctx.sanitizeNames.run' { options := (← getOptions) }
  withLCtx lctx mvarDecl.localInstances do
    -- Flush a pending run of same-type names into one grouped hypothesis.
    let flush : Array ProofHyp → Array String → Option Expr → MetaM (Array ProofHyp) :=
      fun hyps names ty? => do
        match ty? with
        | none    => return hyps
        | some ty =>
          if names.isEmpty then return hyps
          let type ← ppAt ty
          return hyps.push { names, type, value := none, isLet := false }
    let step := fun (acc : Array ProofHyp × Array String × Option Expr)
        (ld : LocalDecl) => do
      let (hyps, names, ty?) := acc
      if ld.isAuxDecl || ld.isImplementationDetail then
        return (hyps, names, ty?)
      match ld with
      -- `cdecl` and a NONDEP `ldecl` are one case, matching `Meta.ppGoal`. A
      -- nondep `ldecl` is a `have`-bound variable: its value is deliberately
      -- opaque, the infoview hides it, and core warns it "might not be type
      -- correct" (`Lean/LocalContext.lean`). Rendering it would both diverge from
      -- the infoview and emit a term the elaborator does not stand behind — the
      -- 30-line `casesOn` blob a `have` produces. So it renders as a plain
      -- hypothesis, value-less and eligible for same-type grouping.
      | .cdecl _ _ n ty .. | .ldecl _ _ n ty _ (nondep := true) .. =>
        let ty ← instantiateMVars ty
        -- Same type as the pending run: extend it rather than starting a new entry.
        if ty? == some ty then
          return (hyps, names.push n.simpMacroScopes.toString, ty?)
        else
          return (← flush hyps names ty?, #[n.simpMacroScopes.toString], some ty)
      -- A genuine (dependent) `let`: the variable IS its value, so the value is
      -- semantically load-bearing and we keep it. It always stands alone.
      | .ldecl _ _ n ty val .. =>
        let hyps ← flush hyps names ty?
        return (hyps.push { names := #[n.simpMacroScopes.toString]
                            type  := ← ppAt (← instantiateMVars ty)
                            value := some (← ppAt (← instantiateMVars val))
                            isLet := true }, #[], none)
    let (hyps, names, ty?) ← lctx.foldlM (init := ((#[] : Array ProofHyp),
      (#[] : Array String), (none : Option Expr))) step
    let hyps ← flush hyps names ty?
    let target ← ppAt (← instantiateMVars mvarDecl.type)
    return some (hyps, target, toString mvarId.name)

/-- Assemble the infoview-shaped block: hypothesis lines then `⊢ target`. -/
def prettyOf (hyps : Array ProofHyp) (target : String) : String :=
  let lines := hyps.toList.map fun h =>
    let ns := " ".intercalate h.names.toList
    match h.value with
    | some v => s!"{ns} : {h.type} := {v}"
    | none   => s!"{ns} : {h.type}"
  "\n".intercalate (lines ++ [s!"⊢ {target}"])

/-! ## The goal table

Goals are interned so a shared state (step `k`'s `goalsAfter` is step `k+1`'s
`goalsBefore`) is stored once and the sharing is visible as a repeated id.

Interning keys on RENDERED CONTENT, not on `MVarId`: the same metavariable renders
differently under different snapshots, so an `MVarId`-keyed cache would hand back
a stale rendering. Content keying is trivially correct. It does not avoid the
render cost — only the wire size; a snapshot-keyed memo could be added later, if
measurement shows it matters. -/

/-- Accumulates the per-record goal table with a content-keyed index. -/
structure GoalTable where
  goals : Array ProofGoal := #[]
  index : Std.HashMap String Nat := {}
  deriving Inhabited

/-- Intern one rendered goal, returning its id. -/
def GoalTable.intern (t : GoalTable) (mvar : String) (hyps : Array ProofHyp)
    (target : String) : GoalTable × Nat :=
  let pretty := prettyOf hyps target
  -- The mvar name participates in the key only through `pretty`'s content; two
  -- distinct metavariables with identical contexts and targets are genuinely the
  -- same goal state and should share an entry.
  match t.index[pretty]? with
  | some id => (t, id)
  | none =>
    let id := t.goals.size
    ({ goals := t.goals.push { id, mvar, hyps, target, pretty }
       index := t.index.insert pretty id }, id)

/-! ## The walk -/

/-- The tactic-node kinds a user can write: the `tactic` and `conv` parser
categories, read from the file's own environment. See the module docstring for why
this is the selection test. -/
def tacticKindSet (env : Environment) : Std.HashSet Name := Id.run do
  let mut out : Std.HashSet Name := {}
  for cat in [`tactic, `conv] do
    if let some c := Lean.Parser.getParserCategory? env cat then
      out := c.kinds.foldl (fun s k _ => s.insert k) out
  return out

/-- Render a goal list under an ALREADY-RESTORED metavariable context, interning
each into the table. The caller is responsible for entering `runMetaM` with the
correct snapshot — that is the discipline rule 1 in the module docstring. -/
private def internGoals (table : GoalTable) (goals : List MVarId)
    : MetaM (GoalTable × Array Nat) := do
  let mut t := table
  let mut ids : Array Nat := #[]
  for g in goals do
    if let some (hyps, target, mvar) ← renderGoal g then
      let (t', id) := t.intern mvar hyps target
      t := t'
      unless ids.contains id do
        ids := ids.push id
  return (t, ids)

/-- Walk one command's `InfoTree`, returning the kept-tactic forest grouped by
enclosing declaration, plus the goal tables.

Grouping is by `ContextInfo.parentDecl?` — the same attribution
`Corpus.GrindInProof` uses — so mutual blocks and `where` auxiliaries land on the
right declaration rather than on the command.

A goal table is shared across every step of one declaration, so it cannot live in
`visitM`'s per-node accumulator (which flows bottom-up, with siblings invisible to
each other). It lives in an `IO.Ref` keyed by owner instead — local to this call,
never escaping. The forest itself does flow through the accumulator, which is what
makes reparenting free. -/
partial def walkTree (kinds : Std.HashSet Name) (tree : InfoTree)
    : IO (Std.HashMap Name (Array RawStep × GoalTable)) := do
  let tables ← IO.mkRef (∅ : Std.HashMap Name GoalTable)
  let forest? ← tree.visitM (α := Array (Name × RawStep))
    (postNode := fun ctx info _ children => do
      -- Children arrive as a forest of (owner, step) pairs; a dropped node just
      -- passes them through, which is what reparents them onto the nearest kept
      -- ancestor.
      let kids : Array (Name × RawStep) :=
        (children.filterMap id).foldl (· ++ ·) #[]
      let .ofTacticInfo ti := info | return kids
      unless kinds.contains ti.stx.getKind do return kids
      let some rg := ti.stx.getRange? (canonicalOnly := true) | return kids
      let owner := ctx.parentDecl?.getD Name.anonymous
      -- Render the two goal sets under their OWN snapshots. See rule 1.
      let table := (← tables.get).getD owner {}
      let (table, before) ← ({ ctx with mctx := ti.mctxBefore } : ContextInfo).runMetaM {}
        (internGoals table ti.goalsBefore)
      let (table, after) ← ({ ctx with mctx := ti.mctxAfter } : ContextInfo).runMetaM {}
        (internGoals table ti.goalsAfter)
      tables.modify (·.insert owner table)
      let startPos := ctx.fileMap.toPosition rg.start
      let endPos := ctx.fileMap.toPosition rg.stop
      let step : RawStep := {
        kind        := ti.stx.getKind
        elaborator  := ti.elaborator
        startByte   := rg.start.byteIdx
        endByte     := rg.stop.byteIdx
        startLine   := startPos.line
        startCol    := startPos.column
        endLine     := endPos.line
        endCol      := endPos.column
        goalsBefore := before
        goalsAfter  := after
        children    := kids.map (·.2) }
      return #[(owner, step)])
  -- File the top-level kept steps under their owning declaration, alongside the
  -- table that declaration's goals were interned into.
  let finalTables ← tables.get
  let mut out : Std.HashMap Name (Array RawStep × GoalTable) := ∅
  for (owner, step) in forest?.getD #[] do
    let (steps, _) := out.getD owner (#[], finalTables.getD owner {})
    out := out.insert owner (steps.push step, finalTables.getD owner {})
  return out

/-! ## Per-file collection

The file-level entry point mirrors `GrindInProof.grindInProofCore`: run inside the
file's real `CoreM` (via `Frontend.runCollectorOn`, so `findDeclarationRanges?` and
the `FileMap` line up), walk the InfoTrees, and emit one entry per tactic-proved
theorem. -/

/-- One theorem's trajectory, before the driver attaches the discovery-relative
`file` path. Mirrors the `…Entry` / `…Record` split the other collectors use. -/
structure ProofStateEntry where
  name           : String
  module         : String
  startLine      : Option Nat
  startCol       : Option Nat
  endLine        : Option Nat
  endCol         : Option Nat
  declKind       : String
  proofStartByte : Nat
  proofEndByte   : Nat
  proofSource    : String
  parentDecl     : Option String
  goals          : Array ProofGoal
  initialGoals   : Array Nat
  steps          : Array ProofStep
  stepCount      : Nat
  maxDepth       : Nat
  tacticKinds    : Array String
  hasSorry       : Bool
  outcome        : String
  isPrivate      : Bool
  deriving Inhabited

/-- Every declaration node inside one top-level command, outermost first.

A command usually holds one declaration, but `mutual … end` holds SEVERAL siblings,
and each needs its own proof range. `SourceSyntax.proofRange?` is built on
`findByKind`, which stops at the first match in pre-order, so applying it to a
whole `mutual` command finds only the first theorem's proof — every later one then
fails its `proofRanges` lookup and is dropped from the dataset entirely.

So we descend to the declaration nodes first and range each separately. We stop at
a `declaration` node rather than recursing into it, because its own body may
contain nested `where`/`let rec` declarations whose proof belongs to the enclosing
decl's range, not to a sibling. (`where` auxiliaries still get their own entry:
they are lifted to their own constants with their own `findDeclarationRanges?`, and
`declarationKeys` files them under a distinct key.)

Recognition is by NODE KIND, deliberately not by `declarationId? .isSome`. That
test reports `some` for any ancestor containing a `declId` — including a `mutual`
block and the anonymous `null` wrapper holding its members — so a
`declarationId?`-guarded walk halts above the members and finds one "declaration"
where there are two. -/
partial def declarationNodes (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Command.declaration then #[stx]
  else match stx with
    | .node _ _ args => args.foldl (fun acc a => acc ++ declarationNodes a) #[]
    | _              => #[]

/-- Every `where` / `let rec` auxiliary node in one command.

An auxiliary is lifted by Lean into its own separately-checked constant with its own
`findDeclarationRanges?`, so it deserves its own record — and frequently it is the
*substantive* lemma, the parent's proof being a one-line `exact aux …`. But it is a
term-level `Term.letRecDecl`, not a `Command.declaration`, so `declarationNodes`
does not see it and `proofRange?` on the enclosing command returns the PARENT's
value. See `SourceSyntax.auxProofRange?`.

Unlike `declarationNodes` this descends fully rather than stopping at the first
hit: auxiliaries can nest (a `let rec` inside an aux's own tactic proof), and one
`where` clause routinely declares several. -/
partial def auxDeclarationNodes (stx : Syntax) (acc : Array Syntax := #[])
    : Array Syntax :=
  let acc := if stx.getKind == ``Lean.Parser.Term.letRecDecl then acc.push stx else acc
  match stx with
  | .node _ _ args => args.foldl (fun a c => auxDeclarationNodes c a) acc
  | _              => acc

/-- One declaration's proof location: its value's byte range, the verbatim text,
and — for a `where`/`let rec` auxiliary — the enclosing declaration's source name. -/
structure ProofLoc where
  startByte  : Nat
  endByte    : Nat
  text       : String
  /-- The enclosing declaration's SOURCE name, for an auxiliary; `none` for a
  top-level declaration. Source-derived rather than parsed out of the constant's
  full name: an aux is named `<parent>.<aux>`, but so is any namespaced theorem, so
  name-splitting would misclassify ordinary declarations as auxiliaries. -/
  parentDecl : Option String := none
  deriving Inhabited

/-- Map each declaration's key position to its proof location, keyed the way
`CorpusManifest.buildSourceMap` keys — by the decl's `findDeclarationRanges?`
selection position — so a constant can look up its own proof. Only declarations
with a value appear.

Covers both top-level declarations and `where`/`let rec` auxiliaries; the two use
different range functions because they are different syntactic forms. -/
def buildProofRangeMap (src : String) (commands : Array Syntax)
    : Std.HashMap (Nat × Nat) ProofLoc := Id.run do
  let fileMap := src.toFileMap
  let mut out : Std.HashMap (Nat × Nat) ProofLoc := {}
  let sliceOf := fun (rg : Lean.Syntax.Range) =>
    (String.Pos.Raw.extract src rg.start rg.stop).trimAsciiEnd.copy
  for cmdStx in commands do
    for declStx in declarationNodes cmdStx do
      -- `proofRange?` gives the range a proof REPLACEMENT would overwrite, which
      -- for `:= term` is the term alone — exactly the `body` span.
      if let some (_, rg) := proofRange? declStx then
        for key in declarationKeys fileMap declStx do
          out := out.insert key
            { startByte := rg.start.byteIdx, endByte := rg.stop.byteIdx
              text := sliceOf rg }
      -- The declaration's own auxiliaries. Their keys are distinct from the
      -- parent's (each `letRecDecl` has its own position), so these never
      -- overwrite the entry above.
      let parentName := (declarationId? declStx).map fun declId =>
        declId[0].getId.toString
      for lrd in auxDeclarationNodes declStx do
        if let some (_, rg) := auxProofRange? lrd then
          for key in declarationKeys fileMap lrd do
            out := out.insert key
              { startByte := rg.start.byteIdx, endByte := rg.stop.byteIdx
                text := sliceOf rg, parentDecl := parentName }
  return out

/-- Build one theorem's entry from its walked forest.

`slice` reads the verbatim source for a byte range. `outcome` is `"skipped_large"`
when the raw tree exceeds `stepCeiling`, in which case no steps are emitted. -/
def buildEntry (src : String) (name : String) (module : String) (declKind : String)
    (isPrivate hasSorry : Bool)
    (ranges : Option (Nat × Nat × Nat × Nat))
    (proofLoc : ProofLoc)
    (forest : Array RawStep) (table : GoalTable) (outcome : String)
    : ProofStateEntry :=
  let slice := fun (a b : Nat) =>
    (String.Pos.Raw.extract src ⟨a⟩ ⟨b⟩).trimAsciiEnd.copy
  let normalized := normalize forest
  let emit := outcome == "ok" && countRaw normalized ≤ stepCeiling
  let outcome := if outcome == "ok" && !emit then "skipped_large" else outcome
  let (steps0, _) := if emit then toProofSteps slice 0 0 normalized else (#[], 0)
  -- Renumber into pre-order so goal 0 is the state the proof opened in, rather
  -- than whatever the bottom-up walk interned last.
  let (goals, steps) := renumberGoals table.goals steps0
  -- The proof's opening state is the first top-level tactic's `goals_before`.
  let initialGoals := (steps[0]?.map (·.goalsBefore)).getD #[]
  { name, module
    startLine := ranges.map (fun (a, _, _, _) => a)
    startCol  := ranges.map (fun (_, b, _, _) => b)
    endLine   := ranges.map (fun (_, _, c, _) => c)
    endCol    := ranges.map (fun (_, _, _, d) => d)
    declKind
    proofStartByte := proofLoc.startByte
    proofEndByte   := proofLoc.endByte
    proofSource    := proofLoc.text
    parentDecl     := proofLoc.parentDecl
    goals        := goals
    initialGoals
    steps
    stepCount    := countSteps steps
    maxDepth     := depthOf steps
    tacticKinds  := kindsOf steps
    hasSorry, outcome, isPrivate }

/-- Collect every tactic-proved theorem's trajectory for one elaborated file.

Returns the entries plus the count of theorems SKIPPED because their proof is a
bare term (no `by`, hence no tactic nodes) — reported rather than emitted as empty
rows, so a consumer never has to distinguish "no tactics" from "not captured".

`deadlineMs` bounds the whole per-file walk (0 disables): once past it, remaining
theorems are emitted with `outcome := "deadline_skipped"` and no steps, so a slow
file loses its tail rather than everything. -/
def collectFile (r : Frontend.ElabResult) (includePrivate : Bool)
    (deadlineMs : Nat := 0) : CoreM (Array ProofStateEntry × Nat) := do
  let env ← getEnv
  let kinds := tacticKindSet env
  let proofRanges := buildProofRangeMap r.source r.commands
  -- Walk every command tree once, accumulating per-declaration forests.
  let mut byOwner : Std.HashMap Name (Array RawStep × GoalTable) := ∅
  for tree in r.trees.toArray do
    for (owner, (steps, table)) in (← walkTree kinds tree).toList do
      match byOwner[owner]? with
      | some (prev, prevTable) =>
        -- One declaration spanning several command trees is unusual but harmless:
        -- concatenate the forests and keep the larger table.
        byOwner := byOwner.insert owner
          (prev ++ steps, if table.goals.size ≥ prevTable.goals.size then table else prevTable)
      | none => byOwner := byOwner.insert owner (steps, table)
  let startMs ← IO.monoMsNow
  let mut out : Array ProofStateEntry := #[]
  let mut skippedTerm := 0
  for vc in (← Verify.verifiedFileConstants) do
    let info := vc.info
    -- Theorems only: a `def`'s value is a term, not a proof trajectory.
    let .thmInfo _ := info | continue
    let isPrivate := Lean.isPrivateName info.name
    if !includePrivate && isPrivate then continue
    if CollectCommon.alwaysSkip env info.name then continue
    -- Range-less synthetic theorems (`.injEq`, `.sizeOf_spec`, …) have no source.
    let some declRanges ← Lean.findDeclarationRanges? info.name | continue
    let key := (declRanges.selectionRange.pos.line, declRanges.selectionRange.pos.column)
    let displayName := (CollectCommon.displayName info.name).toString
    -- No proof range means we could not locate this theorem's value in the parsed
    -- source, so there is nothing to slice steps out of and the record is dropped.
    -- WARN rather than `continue` silently: a source-authored theorem reaching here
    -- is a real gap in `buildProofRangeMap`, and a silent drop is exactly how
    -- `mutual`-block members went missing (only the first member got a range,
    -- because `proofRange?` stops at the first match in a command). If this fires,
    -- some syntactic form is not being descended into.
    let some proofRange := proofRanges[key]? |
      IO.eprintln s!"corpus-extract: proof-states: no proof range for {displayName} \
        at {key.1}:{key.2} in {r.file.relPath}; skipping (its declaration form may \
        not be handled)"
    let (forest, table) := byOwner.getD info.name (#[], {})
    -- A bare-term proof (`:= rfl`) produces no tactic nodes at all.
    if forest.isEmpty then
      skippedTerm := skippedTerm + 1
      continue
    let pastDeadline := deadlineMs != 0 && (← IO.monoMsNow) - startMs ≥ deadlineMs
    let ranges := some (declRanges.range.pos.line, declRanges.range.pos.column,
                        declRanges.range.endPos.line, declRanges.range.endPos.column)
    out := out.push <| buildEntry r.source displayName
      env.mainModule.toString
      (if isPrivate then "private theorem" else "theorem")
      isPrivate (!vc.isSorryFree) ranges proofRange forest table
      (if pastDeadline then "deadline_skipped" else "ok")
  return (out.qsort (fun a b => a.name < b.name), skippedTerm)

/-- The in-process proof-state entry point: for one frontend-elaborated file, walk
its InfoTrees and return one entry per tactic-proved theorem plus the count of
term-proved theorems skipped. Run via `Frontend.runCollectorOn` so the collector
sees the file's true post-elaboration environment and `FileMap`. -/
def proofStatesCore (r : Frontend.ElabResult) (includePrivate : Bool)
    (deadlineMs : Nat := 0) : IO (Array ProofStateEntry × Nat) :=
  Frontend.runCollectorOn r (collectFile r includePrivate deadlineMs)

end Corpus.ProofStates
