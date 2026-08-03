import Corpus.ProofStates
import Corpus.Artifact
import Corpus.SourceSyntax
import Corpus.TestAssert

/-!
Tests for per-step proof-state extraction.

The tree algebra (`normalize` / `mergeSiblings` / `toProofSteps` /
`renumberGoals`) is deliberately `Info`-free — it operates on plain `RawStep`
data — so almost everything here is a pure unit test needing no `Environment`.
That split is the same one `DeclClosureTests` relies on for `projectClosure`.

The parts that genuinely need a real elaboration (node selection by parser
category, goal rendering under the two metavariable snapshots) are covered by the
end-to-end run documented in `docs/proof-state-extraction.md`, plus the
`--proof-states` invocation against `reassemble/TestProject`.
-/

open Lean
open Corpus
open Corpus.ProofStates

namespace ProofStatesTests

open Corpus.TestAssert (assert)

/-- A `RawStep` builder: only the fields a given test cares about. -/
private def raw (startByte endByte : Nat) (kind : String)
    (before after : Array Nat := #[]) (children : Array RawStep := #[])
    (invocations : Nat := 1) : RawStep :=
  { kind := kind.toName, elaborator := `test
    startByte, endByte
    startLine := 1, startCol := startByte, endLine := 1, endCol := endByte
    goalsBefore := before, goalsAfter := after, invocations, children }

/-- A `ProofGoal` builder keyed only by its target, which is all the interning and
renumbering tests need to tell goals apart. -/
private def goal (id : Nat) (target : String) : ProofGoal :=
  { id, mvar := s!"_uniq.{id}", hyps := #[], target, pretty := s!"⊢ {target}" }

/-! ## Sibling merge -/

/-- `all_goals t` / `t <;> u` re-invoke the SAME syntax once per goal, yielding N
siblings at one range. They must collapse to a single step whose goal sets are the
unions and whose `invocations` is N. -/
private def testMergeCombinator : IO Unit := do
  let merged := mergeSiblings #[
    raw 10 14 "simp" (before := #[1]) (after := #[]),
    raw 10 14 "simp" (before := #[2]) (after := #[])]
  assert (merged.size == 1) "two invocations of one syntax did not merge"
  let s := merged[0]!
  assert (s.invocations == 2) s!"expected invocations=2, got {s.invocations}"
  assert (s.goalsBefore == #[1, 2]) s!"goals_before union wrong: {s.goalsBefore}"
  assert (s.goalsAfter == #[]) s!"goals_after union wrong: {s.goalsAfter}"

/-- `repeat t` re-invokes `t` after the goals run out, so one invocation carries an
EMPTY `goalsBefore`. That must not corrupt the union or the count. -/
private def testMergeEmptyInvocation : IO Unit := do
  let merged := mergeSiblings #[
    raw 10 14 "simp" (before := #[3]) (after := #[]),
    raw 10 14 "simp" (before := #[]) (after := #[])]
  assert (merged.size == 1) "repeat-style invocations did not merge"
  let s := merged[0]!
  assert (s.goalsBefore == #[3]) s!"empty invocation polluted the union: {s.goalsBefore}"
  assert (s.invocations == 2) s!"expected invocations=2, got {s.invocations}"

/-- Merging keys on `(range, kind)`. Siblings differing in either are distinct
tactics and must survive separately — otherwise `simp; simp` on two lines, or two
different tactics sharing a range, would silently collapse. -/
private def testMergeDiscriminates : IO Unit := do
  let byRange := mergeSiblings #[
    raw 10 14 "simp" (before := #[1]),
    raw 20 24 "simp" (before := #[2])]
  assert (byRange.size == 2) "siblings at different ranges were merged"
  let byKind := mergeSiblings #[
    raw 10 14 "simp" (before := #[1]),
    raw 10 14 "omega" (before := #[2])]
  assert (byKind.size == 2) "siblings of different kinds were merged"

/-- Children merge too, at every depth. -/
private def testMergeNested : IO Unit := do
  let normalized := normalize #[
    raw 0 30 "allGoals" (before := #[0]) (children := #[
      raw 10 14 "simp" (before := #[1]),
      raw 10 14 "simp" (before := #[2])])]
  assert (normalized.size == 1) "top-level step count changed"
  let kids := normalized[0]!.children
  assert (kids.size == 1) s!"nested siblings did not merge: {kids.size}"
  -- Order matters: the union must follow the order the tactic ran on the goals
  -- (elaboration order), not an order imposed by sorting tied siblings. A sort
  -- placed BEFORE the merge silently reversed this.
  assert (kids[0]!.goalsBefore == #[1, 2])
    s!"nested goal union wrong (order-sensitive): {kids[0]!.goalsBefore}"

/-- The merged goal union must preserve invocation order even when the sort would
tie the siblings — `normalize` must merge before it sorts. -/
private def testMergePreservesGoalOrder : IO Unit := do
  let normalized := normalize #[
    raw 10 14 "simp" (before := #[7]),
    raw 10 14 "simp" (before := #[3]),
    raw 10 14 "simp" (before := #[5])]
  assert (normalized.size == 1) "invocations did not merge"
  assert (normalized[0]!.goalsBefore == #[7, 3, 5])
    s!"goal order not preserved through normalize: {normalized[0]!.goalsBefore}"

/-! ## Ordering -/

/-- `visitM` returns children in ELABORATION order, which for a combinator is goal
order, not source order. Normalization must restore source order so the emitted
tree reads like the proof text. -/
private def testOrdering : IO Unit := do
  let normalized := normalize #[
    raw 30 34 "third", raw 10 14 "first", raw 20 24 "second"]
  let kinds := normalized.map (·.kind.toString)
  assert (kinds == #["first", "second", "third"])
    s!"siblings not ordered by start_byte: {kinds}"

/-- Ties on `startByte` still yield a total, deterministic order (`qsort` is not
stable), so two runs cannot disagree. -/
private def testOrderingDeterministic : IO Unit := do
  let a := normalize #[raw 10 20 "bbb", raw 10 14 "aaa", raw 10 20 "aaa"]
  let b := normalize #[raw 10 20 "aaa", raw 10 20 "bbb", raw 10 14 "aaa"]
  assert (a.map (·.kind.toString) == b.map (·.kind.toString))
    "tied siblings ordered differently across permutations"
  assert (a.size == 3) s!"tied distinct siblings collapsed: {a.size}"

/-! ## Indexing and shape -/

/-- `index` must be dense pre-order and `depth` must match nesting, because both
are how a consumer reconstructs the tree from a flattened view. -/
private def testIndexing : IO Unit := do
  let slice := fun (_ _ : Nat) => "t"
  let (steps, next) := toProofSteps slice 0 0 #[
    raw 0 40 "outer" (children := #[
      raw 5 10 "innerA" (children := #[raw 6 8 "leaf"]),
      raw 20 25 "innerB"]),
    raw 50 55 "tail"]
  assert (next == 5) s!"expected 5 steps allocated, got {next}"
  let outer := steps[0]!
  assert (outer.index == 0 && outer.depth == 0) "root index/depth wrong"
  let innerA := outer.children[0]!
  assert (innerA.index == 1 && innerA.depth == 1) "child index/depth wrong"
  assert (innerA.children[0]!.index == 2 && innerA.children[0]!.depth == 2)
    "grandchild index/depth wrong"
  assert (outer.children[1]!.index == 3) "second child index not pre-order"
  assert (steps[1]!.index == 4 && steps[1]!.depth == 0) "tail index/depth wrong"
  assert (countSteps steps == 5) s!"countSteps wrong: {countSteps steps}"
  assert (depthOf steps == 2) s!"depthOf wrong: {depthOf steps}"

/-- `tactic_kinds` is the sorted distinct set across the WHOLE tree, nested
children included — it exists so a consumer can filter without walking. -/
private def testKinds : IO Unit := do
  let slice := fun (_ _ : Nat) => "t"
  let (steps, _) := toProofSteps slice 0 0 #[
    raw 0 40 "zeta" (children := #[raw 5 10 "alpha", raw 20 25 "zeta"])]
  let ks := kindsOf steps
  assert (ks == #["alpha", "zeta"]) s!"kindsOf wrong: {ks}"

/-- Each step's `tactic` is sliced from the source by its own byte range, so the
text is verbatim rather than pretty-printed. -/
private def testSlicing : IO Unit := do
  let src := "by\n  simp\n"
  let slice := fun (a b : Nat) =>
    (String.Pos.Raw.extract src ⟨a⟩ ⟨b⟩).trimAsciiEnd.copy
  let (steps, _) := toProofSteps slice 0 0 #[raw 5 9 "simp"]
  assert (steps[0]!.tactic == "simp") s!"slice wrong: {steps[0]!.tactic}"

/-! ## Reparenting

A dropped node (a `tacticSeq`, a `null`, an uncategorized macro expansion) returns
its children's forest unchanged, so they attach to the nearest KEPT ancestor. The
walk does that structurally; these assert the invariant it must preserve — no
orphans, no invented nodes. -/

/-- Reparented grandchildren must all survive, exactly once each. -/
private def testReparentPreservesEveryNode : IO Unit := do
  -- What the walk produces when a container between `outer` and its two tactics
  -- was dropped: both land directly on `outer`.
  let normalized := normalize #[
    raw 0 40 "outer" (children := #[raw 5 10 "a", raw 20 25 "b"])]
  let kids := normalized[0]!.children
  assert (kids.size == 2) s!"reparented children lost or duplicated: {kids.size}"
  assert (kids.map (·.kind.toString) == #["a", "b"]) "reparented children misordered"

/-! ## Goal renumbering

`visitM` is bottom-up, so goals intern deepest-first and the OPENING goal gets the
highest id. Renumbering into step pre-order makes goal 0 the state the proof opened
in, which is what `initial_goals` must point at. -/

/-- Renumbering puts the first-referenced goal at id 0 and rewrites every
reference consistently. -/
private def testRenumber : IO Unit := do
  let slice := fun (_ _ : Nat) => "t"
  -- Interned bottom-up: goal 2 is the opening state, 0 and 1 are the branches.
  let (steps, _) := toProofSteps slice 0 0 #[
    raw 0 40 "induction" (before := #[2]) (after := #[]) (children := #[
      raw 5 10 "rfl" (before := #[0]),
      raw 20 25 "simp" (before := #[1])])]
  let goals := #[goal 0 "branchA", goal 1 "branchB", goal 2 "opening"]
  let (goals', steps') := renumberGoals goals steps
  assert (goals'.size == 3) s!"renumber lost goals: {goals'.size}"
  assert (goals'[0]!.target == "opening")
    s!"goal 0 is not the opening state: {goals'[0]!.target}"
  assert (goals'[0]!.id == 0 && goals'[1]!.id == 1 && goals'[2]!.id == 2)
    "renumbered ids are not dense"
  assert (steps'[0]!.goalsBefore == #[0]) "root reference not remapped to 0"
  let kids := steps'[0]!.children
  assert (kids[0]!.goalsBefore == #[1] && kids[1]!.goalsBefore == #[2])
    "child references not remapped in pre-order"

/-- A goal the final tree no longer references is dropped, so the table cannot
carry orphans a consumer would have to explain. -/
private def testRenumberDropsOrphans : IO Unit := do
  let slice := fun (_ _ : Nat) => "t"
  let (steps, _) := toProofSteps slice 0 0 #[raw 0 10 "simp" (before := #[1])]
  let goals := #[goal 0 "orphan", goal 1 "used"]
  let (goals', steps') := renumberGoals goals steps
  assert (goals'.size == 1) s!"orphan goal retained: {goals'.size}"
  assert (goals'[0]!.target == "used") "wrong goal survived"
  assert (steps'[0]!.goalsBefore == #[0]) "surviving reference not remapped"

/-! ## Goal interning -/

/-- Identical rendered states collapse to one entry (that is the wire-size win and
makes sharing visible); differing states do not. Interning keys on rendered
CONTENT, never on the metavariable name — the same mvar renders differently under
different snapshots. -/
private def testInterning : IO Unit := do
  let t : GoalTable := {}
  let hyp : ProofHyp := { names := #["n"], type := "Nat", value := none, isLet := false }
  let (t, a) := t.intern "_uniq.1" #[hyp] "P n"
  let (t, b) := t.intern "_uniq.99" #[hyp] "P n"
  assert (a == b) "identical goal states did not share an id"
  assert (t.goals.size == 1) s!"identical states created {t.goals.size} entries"
  let (t, c) := t.intern "_uniq.1" #[hyp] "Q n"
  assert (c != a) "different targets shared an id"
  let (t, d) := t.intern "_uniq.1" #[] "P n"
  assert (d != a) "different hypothesis sets shared an id"
  assert (t.goals.size == 3) s!"expected 3 distinct goals, got {t.goals.size}"

/-- `pretty` is synthesized from `hyps`/`target`, so it cannot drift from them. -/
private def testPretty : IO Unit := do
  let plain : ProofHyp := { names := #["a", "b"], type := "Nat", value := none, isLet := false }
  let letH : ProofHyp := { names := #["x"], type := "Nat", value := some "3", isLet := true }
  assert (prettyOf #[plain] "a = b" == "a b : Nat\n⊢ a = b")
    s!"grouped hypothesis rendering wrong: {prettyOf #[plain] "a = b"}"
  assert (prettyOf #[letH] "True" == "x : Nat := 3\n⊢ True")
    s!"let-binding rendering wrong: {prettyOf #[letH] "True"}"
  assert (prettyOf #[] "True" == "⊢ True") "empty context rendering wrong"

/-! ## `have` vs `let` in the local context

A `have`-bound hypothesis is a NONDEP `ldecl`: its value is deliberately opaque,
the infoview hides it, and core warns it "might not be type correct". Rendering it
emitted the whole `casesOn` proof term the elaborator built — divergent from the
infoview and 41% of the output on a real corpus. `renderGoal` therefore treats a
nondep `ldecl` exactly as `Meta.ppGoal` does: like a `cdecl`.

`renderGoal` needs a `MetaM`, so this asserts the shape the fix must produce via
the same `prettyOf` the record uses; the live behaviour is covered by the
end-to-end run. -/

/-- A `have`-bound hypothesis carries no value and may share a same-type run; a
genuine `let` keeps its value and stands alone. -/
private def testHaveVsLet : IO Unit := do
  -- What a nondep `ldecl` (a `have`) must look like after rendering: no value, so
  -- it groups with a same-type neighbour exactly like any other hypothesis.
  let haveH : ProofHyp := { names := #["h1", "h2"], type := "P n", value := none, isLet := false }
  assert (prettyOf #[haveH] "Q n" == "h1 h2 : P n\n⊢ Q n")
    s!"have-bound rendering wrong: {prettyOf #[haveH] "Q n"}"
  assert (haveH.value == none) "a have-bound hypothesis must not carry a value"
  -- A dependent `let` is semantically its value, so the value is retained.
  let letH : ProofHyp := { names := #["x"], type := "Nat", value := some "3", isLet := true }
  assert (letH.isLet && letH.value == some "3") "a let-binding must keep its value"
  assert (prettyOf #[letH] "True" == "x : Nat := 3\n⊢ True")
    s!"let rendering wrong: {prettyOf #[letH] "True"}"

/-! ## The step ceiling -/

/-- `countRaw` counts the whole tree, since it is what the size pre-filter tests
against `stepCeiling` before any goal is rendered. -/
private def testCountRaw : IO Unit := do
  let tree := #[
    raw 0 40 "outer" (children := #[raw 5 10 "a" (children := #[raw 6 8 "b"])]),
    raw 50 55 "tail"]
  assert (countRaw tree == 4) s!"countRaw wrong: {countRaw tree}"

/-- Over `stepCeiling`, the record is emitted with `skipped_large` and NO steps or
goals — the size pre-filter must refuse the work rather than render thousands of
goals. Under it, the record is `ok` and complete. -/
private def testStepCeiling : IO Unit := do
  let big := (List.range (stepCeiling + 5)).toArray.map fun i =>
    raw (i * 10) (i * 10 + 4) s!"t{i}" (before := #[0])
  let table := (({} : GoalTable).intern "m" #[] "T").1
  let over := buildEntry "src" "N" "M" "theorem" false false none { startByte := 0, endByte := 3, text := "by" } big table "ok"
  assert (over.outcome == "skipped_large")
    s!"over-ceiling outcome wrong: {over.outcome}"
  assert (over.stepCount == 0 && over.goals.isEmpty)
    "an over-ceiling record must carry no steps or goals"
  let under := buildEntry "src" "N" "M" "theorem" false false none { startByte := 0, endByte := 3, text := "by" }
    (big.extract 0 3) table "ok"
  assert (under.outcome == "ok" && under.stepCount == 3)
    s!"under-ceiling record wrong: {under.outcome}/{under.stepCount}"
  -- A non-`ok` outcome passed in (the deadline path) is preserved, not overwritten.
  let dl := buildEntry "src" "N" "M" "theorem" false false none { startByte := 0, endByte := 3, text := "by" }
    (big.extract 0 3) table "deadline_skipped"
  assert (dl.outcome == "deadline_skipped" && dl.stepCount == 0)
    s!"deadline outcome not preserved: {dl.outcome}/{dl.stepCount}"

/-! ## Declaration descent

A `mutual … end` command holds SEVERAL declarations. `SourceSyntax.proofRange?` is
built on `findByKind`, which stops at the first pre-order match, so applying it to a
whole `mutual` command finds only the first theorem's proof — every later member
then fails its proof-range lookup and vanishes from the dataset. `declarationNodes`
descends to the members first.

Recognition must be by node KIND: `declarationId? .isSome` is `some` for any
ancestor containing a `declId`, including the `mutual` block and the anonymous
`null` wrapper around its members, so a `declarationId?`-guarded walk halts above
the members and reports one declaration where there are two. -/

/-- A `mutual` block yields one node per member, not one for the block. -/
private unsafe def testDeclarationNodes : IO Unit := do
  let src := "mutual\n  theorem a : True := by trivial\n  theorem b : True := by trivial\nend\n"
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Init }] {} (trustLevel := 1024) (loadExts := true)
  let inputCtx := Lean.Parser.mkInputContext src "<test>"
  let (header, parserState, msgs) ← Lean.Parser.parseHeader inputCtx
  let _ := header
  let s ← Lean.Elab.IO.processCommands inputCtx parserState
    (Lean.Elab.Command.mkState env msgs {})
  let mutuals := s.commands.filter (·.getKind == ``Lean.Parser.Command.mutual)
  assert (mutuals.size == 1) s!"expected one mutual command, got {mutuals.size}"
  let nodes := declarationNodes mutuals[0]!
  assert (nodes.size == 2)
    s!"mutual block yielded {nodes.size} declaration node(s), expected 2"
  for n in nodes do
    assert (n.getKind == ``Lean.Parser.Command.declaration)
      s!"descent returned a non-declaration node: {n.getKind}"
    assert (SourceSyntax.proofRange? n).isSome
      "a mutual member has no proof range; its record would be dropped"
  -- Distinct keys: a shared key would make one member overwrite the other.
  let fileMap := src.toFileMap
  let keys := nodes.flatMap (SourceSyntax.declarationKeys fileMap)
  assert (keys.size == 2 && keys[0]! != keys[1]!)
    s!"mutual members did not get distinct proof-range keys: {keys}"
  -- A plain single declaration still yields exactly itself.
  let plains := s.commands.filter (·.getKind == ``Lean.Parser.Command.declaration)
  for c in plains do
    assert ((declarationNodes c).size == 1) "a plain declaration did not yield exactly one node"

/-! ## `where` / `let rec` auxiliaries

An auxiliary is lifted into its own separately-checked constant and deserves its own
record — often it IS the substantive lemma, the parent's proof being a one-line
`exact aux …`. But it is a term-level `Term.letRecDecl`, not a
`Command.declaration`, so `declarationNodes` cannot see it and `proofRange?` on the
enclosing command returns the PARENT's value. `auxDeclarationNodes` +
`auxProofRange?` close that. -/

/-- Both auxiliary value forms are recognized and classified the way `proofRange?`
classifies the corresponding top-level forms, with the value node's own range. -/
private unsafe def testAuxProofRange : IO Unit := do
  let src := "theorem t : True := by exact a\nwhere\n  a : True := by trivial\n"
  let eqnSrc := "def d (n : Nat) : Nat := go n\nwhere\n  go : Nat → Nat\n    | 0 => 0\n    | k+1 => k\n"
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Init }] {} (trustLevel := 1024) (loadExts := true)
  let parse := fun (s : String) => do
    let inputCtx := Lean.Parser.mkInputContext s "<test>"
    let (_, parserState, msgs) ← Lean.Parser.parseHeader inputCtx
    let st ← Lean.Elab.IO.processCommands inputCtx parserState
      (Lean.Elab.Command.mkState env msgs {})
    pure st.commands
  -- `letIdDecl` (`:= term`) → `.simple`, ranging the term alone.
  let cmds ← parse src
  let auxes := cmds.flatMap auxDeclarationNodes
  assert (auxes.size == 1) s!"expected one aux node, got {auxes.size}"
  let some (kind, rg) := SourceSyntax.auxProofRange? auxes[0]!
    | throw <| IO.userError "auxProofRange? found no range for a letIdDecl aux"
  assert (kind == .simple) s!"letIdDecl should classify as .simple, got {repr kind}"
  let text := (String.Pos.Raw.extract src rg.start rg.stop).trimAsciiEnd.copy
  assert (text == "by trivial") s!"aux value range wrong: {text}"
  -- `letEqnsDecl` (match alternatives) → `.equations`.
  let eqnCmds ← parse eqnSrc
  let eqnAuxes := eqnCmds.flatMap auxDeclarationNodes
  assert (eqnAuxes.size == 1) s!"expected one equation aux, got {eqnAuxes.size}"
  let some (eqnKind, eqnRg) := SourceSyntax.auxProofRange? eqnAuxes[0]!
    | throw <| IO.userError "auxProofRange? found no range for a letEqnsDecl aux"
  assert (eqnKind == .equations)
    s!"letEqnsDecl should classify as .equations, got {repr eqnKind}"
  let eqnText := (String.Pos.Raw.extract eqnSrc eqnRg.start eqnRg.stop).trimAsciiEnd.copy
  assert (eqnText.startsWith "| 0 => 0")
    s!"equation aux range should span the alternatives, got: {eqnText}"

/-- Several auxiliaries in one `where` clause each get their own node and a DISTINCT
key, so one cannot overwrite another in the proof-range map. A command with no
auxiliary yields none. -/
private unsafe def testAuxDeclarationNodes : IO Unit := do
  let src := "theorem t : True := by exact (a.intro b)\nwhere\n  a : True := by trivial\n  b : True := by trivial\ntheorem plain : True := by trivial\n"
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Init }] {} (trustLevel := 1024) (loadExts := true)
  let inputCtx := Lean.Parser.mkInputContext src "<test>"
  let (_, parserState, msgs) ← Lean.Parser.parseHeader inputCtx
  let st ← Lean.Elab.IO.processCommands inputCtx parserState
    (Lean.Elab.Command.mkState env msgs {})
  let fileMap := src.toFileMap
  let withAux := st.commands.filter (fun c => !(auxDeclarationNodes c).isEmpty)
  assert (withAux.size == 1) s!"expected one command with auxes, got {withAux.size}"
  let auxes := auxDeclarationNodes withAux[0]!
  assert (auxes.size == 2) s!"expected two auxes in one where clause, got {auxes.size}"
  let keys := auxes.flatMap (SourceSyntax.declarationKeys fileMap)
  assert (keys.size == 2 && keys[0]! != keys[1]!)
    s!"auxes must get distinct keys or one overwrites the other: {keys}"
  -- The map must contain the parent AND both auxes: three separate entries.
  let m := buildProofRangeMap src st.commands
  assert (m.size ≥ 3) s!"proof-range map lost an entry: size={m.size}"
  -- Each aux entry records its parent; the parent's own entry does not.
  let auxLocs := keys.filterMap (m[·]?)
  assert (auxLocs.size == 2) "aux entries missing from the proof-range map"
  for loc in auxLocs do
    assert (loc.parentDecl == some "t")
      s!"aux parentDecl wrong: {loc.parentDecl}"
  -- A plain theorem contributes an entry with no parent.
  let plains := st.commands.filter (fun c =>
    (auxDeclarationNodes c).isEmpty && !(declarationNodes c).isEmpty)
  assert (!plains.isEmpty) "expected a plain declaration command"
  let plainKeys := (declarationNodes plains[0]!).flatMap (SourceSyntax.declarationKeys fileMap)
  let plainLocs := plainKeys.filterMap (m[·]?)
  assert (!plainLocs.isEmpty) "plain declaration missing from the map"
  for loc in plainLocs do
    assert (loc.parentDecl == none)
      s!"a top-level declaration must have no parentDecl, got {loc.parentDecl}"

/-! ## Wire format -/

/-- Round-trip through JSON, including the recursive `children` and the nested
goal/hypothesis objects. -/
private def testRoundTrip : IO Unit := do
  let rec_ : ProofStateRecord := {
    name := "P.thm", module := "P.Basic", file := some "P/Basic.lean"
    startLine := some 3, startCol := some 0, endLine := some 5, endCol := some 9
    declKind := "theorem"
    proofStartByte := 20, proofEndByte := 44, proofSource := "by\n  induction n"
    parentDecl := some "outer"
    goals := #[{ id := 0, mvar := "_uniq.1"
                 hyps := #[{ names := #["n"], type := "Nat", value := none, isLet := false }]
                 target := "P n", pretty := "n : Nat\n⊢ P n" }]
    initialGoals := #[0]
    steps := #[{ index := 0, depth := 0, tactic := "induction n"
                 tacticKind := "Lean.Parser.Tactic.induction", elaborator := "evalInduction"
                 startLine := 4, startCol := 2, endLine := 4, endCol := 13
                 startByte := 25, endByte := 36
                 goalsBefore := #[0], goalsAfter := #[], invocations := 1
                 children := #[{ index := 1, depth := 1, tactic := "rfl"
                                 tacticKind := "Lean.Parser.Tactic.tacticRfl"
                                 elaborator := "evalRfl"
                                 startLine := 5, startCol := 4, endLine := 5, endCol := 7
                                 startByte := 40, endByte := 43
                                 goalsBefore := #[0], goalsAfter := #[]
                                 invocations := 2, children := #[] }] }]
    stepCount := 2, maxDepth := 1
    tacticKinds := #["Lean.Parser.Tactic.induction", "Lean.Parser.Tactic.tacticRfl"]
    hasSorry := false, outcome := "ok", isPrivate := false }
  let json := ProofStateRecord.toJson rec_
  match ProofStateRecord.fromJson? json with
  | .error e => throw <| IO.userError s!"round-trip decode failed: {e}"
  | .ok back =>
    assert (back.name == rec_.name && back.module == rec_.module) "identity fields lost"
    assert (back.proofStartByte == 20 && back.proofEndByte == 44) "byte offsets lost"
    assert (back.parentDecl == some "outer") s!"parent_decl lost: {back.parentDecl}"
    assert (back.goals.size == 1 && back.goals[0]!.hyps == rec_.goals[0]!.hyps)
      "goal hypotheses lost"
    assert (back.goals[0]!.pretty == rec_.goals[0]!.pretty) "goal pretty lost"
    assert (back.steps.size == 1) "steps lost"
    assert (back.steps[0]!.tactic == "induction n") "step tactic lost"
    assert (back.steps[0]!.children.size == 1) "nested child lost"
    assert (back.steps[0]!.children[0]!.tactic == "rfl") "nested tactic lost"
    assert (back.steps[0]!.children[0]!.invocations == 2) "nested invocations lost"
    assert (back.stepCount == 2 && back.maxDepth == 1) "shape counters lost"
    assert (back.tacticKinds == rec_.tacticKinds) "tactic kinds lost"
    assert (back.outcome == "ok" && !back.hasSorry) "outcome flags lost"
  -- The wire form must also survive the JSONL reader consumers actually use.
  let line := (Lean.toJson rec_).compress ++ "\n"
  match Artifact.parseJsonl (α := ProofStateRecord) line with
  | .error e => throw <| IO.userError s!"JSONL parse failed: {e}"
  | .ok arr =>
    assert (arr.size == 1 && arr[0]!.name == "P.thm") "JSONL round-trip lost the record"

/-- Golden key set: the wire schema is a published contract, so an accidental
rename or drop must fail loudly rather than silently change the dataset. -/
private def testGoldenKeys : IO Unit := do
  let expectedRecord := #[
    "decl_kind", "end_col", "end_line", "file", "goals", "has_sorry",
    "initial_goals", "is_private", "max_depth", "module", "name", "outcome",
    "parent_decl", "proof_end_byte", "proof_source", "proof_start_byte", "start_col",
    "start_line", "step_count", "steps", "tactic_kinds"]
  let expectedStep := #[
    "children", "depth", "elaborator", "end_byte", "end_col", "end_line",
    "goals_after", "goals_before", "index", "invocations", "start_byte",
    "start_col", "start_line", "tactic", "tactic_kind"]
  let expectedGoal := #["hyps", "id", "mvar", "pretty", "target"]
  let expectedHyp := #["is_let", "names", "type", "value"]
  -- `Json.obj` is backed by a sorted map, so `keys` is already alphabetical —
  -- which is also the on-wire order (see `Corpus.Records`' encoder docstring).
  let keysOf (j : Json) : Array String :=
    match j with
    | .obj kvs => kvs.keys.toArray
    | _        => #[]
  let hyp : ProofHyp := { names := #["n"], type := "Nat", value := none, isLet := false }
  let g : ProofGoal := { id := 0, mvar := "m", hyps := #[hyp], target := "T", pretty := "⊢ T" }
  let s : ProofStep := { index := 0, depth := 0, tactic := "simp"
                         tacticKind := "k", elaborator := "e"
                         startLine := 1, startCol := 0, endLine := 1, endCol := 4
                         startByte := 0, endByte := 4
                         goalsBefore := #[0], goalsAfter := #[]
                         invocations := 1, children := #[] }
  let r : ProofStateRecord := { name := "n", module := "m", file := none
                                startLine := none, startCol := none
                                endLine := none, endCol := none
                                declKind := "theorem"
                                proofStartByte := 0, proofEndByte := 4
                                proofSource := "by simp", parentDecl := none
                                goals := #[g], initialGoals := #[0], steps := #[s]
                                stepCount := 1, maxDepth := 0, tacticKinds := #["k"]
                                hasSorry := false, outcome := "ok", isPrivate := false }
  assert (keysOf (ProofHyp.toJson hyp) == expectedHyp)
    s!"ProofHyp keys changed: {keysOf (ProofHyp.toJson hyp)}"
  assert (keysOf (ProofGoal.toJson g) == expectedGoal)
    s!"ProofGoal keys changed: {keysOf (ProofGoal.toJson g)}"
  assert (keysOf (ProofStep.toJson s) == expectedStep)
    s!"ProofStep keys changed: {keysOf (ProofStep.toJson s)}"
  assert (keysOf (ProofStateRecord.toJson r) == expectedRecord)
    s!"ProofStateRecord keys changed: {keysOf (ProofStateRecord.toJson r)}"

/-! ## Node-selection guard

The design drops the macro-collapse rule on the evidence that a macro expansion
is never BOTH in a tactic parser category AND canonically ranged — so the
outermost author form survives on its own. That is an empirical claim about Lean's
elaborators, so it gets an explicit guard: this asserts the invariant the rule's
absence depends on, using the real `tactic`/`conv` category sets. -/

/-- The container and glue kinds the raw tree carries must NOT be in the tactic or
conv categories — that non-membership is exactly what makes the category test a
sufficient filter. `Lean.cdot` and real tactics must be in it. -/
private unsafe def testCategoryFilter : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Init }] {} (trustLevel := 1024) (loadExts := true)
  let kinds := tacticKindSet env
  -- Structure and glue: dropped by the category test.
  for k in [``Lean.Parser.Tactic.tacticSeq, ``Lean.Parser.Tactic.tacticSeq1Indented,
            ``Lean.Parser.Tactic.tacticSeqBracketed, ``Lean.Parser.Term.byTactic,
            `Lean.cdotTk, `null, `by, `«;», `«<;>»] do
    assert (!kinds.contains k) s!"{k} is in a tactic category; the filter would keep it"
  -- Real author-written tactics, combinators included: kept.
  for k in [``Lean.Parser.Tactic.simp, ``Lean.Parser.Tactic.allGoals,
            ``Lean.Parser.Tactic.induction, `Lean.cdot,
            ``Lean.Parser.Tactic.tacticTrivial, ``Lean.Parser.Tactic.tacticRfl,
            ``Lean.Parser.Tactic.Conv.conv] do
    assert (kinds.contains k) s!"{k} is not in a tactic category; the filter would drop it"
  -- `conv` interiors live in the `conv` category, which is why both are unioned.
  assert (kinds.contains ``Lean.Parser.Tactic.Conv.lhs)
    "conv interior missing; the conv category is not being unioned in"

unsafe def run : IO UInt32 := do
  testMergeCombinator
  testMergeEmptyInvocation
  testMergeDiscriminates
  testMergeNested
  testMergePreservesGoalOrder
  testOrdering
  testOrderingDeterministic
  testIndexing
  testKinds
  testSlicing
  testReparentPreservesEveryNode
  testRenumber
  testRenumberDropsOrphans
  testInterning
  testPretty
  testHaveVsLet
  testCountRaw
  testStepCeiling
  testDeclarationNodes
  testAuxProofRange
  testAuxDeclarationNodes
  testRoundTrip
  testGoldenKeys
  testCategoryFilter
  IO.println "proof state tests passed"
  return (0 : UInt32)

end ProofStatesTests

unsafe def main : IO UInt32 :=
  ProofStatesTests.run
