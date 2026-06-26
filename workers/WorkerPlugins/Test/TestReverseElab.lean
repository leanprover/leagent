import WorkerPlugins.ReverseElab

/-!
Self-contained tests for `WorkerPlugins.ReverseElab`.
-/

namespace WorkerPlugins.Test
open Lean Lean.Meta Lean.Elab Lean.Elab.Term WorkerPlugins.ReverseElab

-- Simple proofs covering the intended cases.
theorem imp_self (p : Prop) (h : p) : p := h
theorem imp_chain (p q : Prop) (h : p → q) (hp : p) : q := h hp
theorem refl_eq : (1 : Nat) + 1 = 2 := rfl
theorem all_intro : ∀ (n : Nat), n = n := fun _ => rfl
theorem and_proj (p q : Prop) (h : p ∧ q) : p := h.1
theorem const_fn (p q : Prop) (hp : p) (_hq : q) : p := hp

/-- Reverse-elaborate the proof term of a named theorem in this module. -/
def testOne (n : Name) : MetaM String := do
  let env ← getEnv
  let some ci := env.find? n | return s!"{n}: <not found>"
  let some v := ci.value? (allowOpaque := true) | return s!"{n}: <no value>"
  let r ← reverseProof ci.type v
  return s!"━━ {n}  [method: {r.method}]\n{r.script}"

/-- Command wrapper so we can `#eval` the MetaM tester from command context. -/
def runTests : MetaM (Array String) := do
  let names : Array Name :=
    #[``imp_self, ``imp_chain, ``refl_eq, ``all_intro, ``and_proj, ``const_fn]
  names.mapM testOne

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let res ← Lean.Elab.Command.liftTermElabM runTests
  for line in res do
    Lean.logInfo line

/-!
Harder reverse-elaboration cases: proofs whose *terms* contain the automation
residue seen in the real corpus (rw→`Eq.mpr`/`congrArg`, simp, omega, decide,
cases→`casesOn`/`Or.casesOn`, `match`, `let`). These should NOT decompose into
the automation tactic (we don't reverse those); the verifier should keep them
as a verified `exact`/`intro_exact`/`exact_whole`, never `fail`.
-/

-- rw residue: Eq.mpr / congrArg chain
theorem rw_case (a b : Nat) (h : a = b) : a + 0 = b := by rw [h]; simp
-- omega: large opaque Lean.Omega.* term
theorem omega_case (n : Nat) : n + 1 > n := by omega
-- decide: of_decide_eq_true (Eq.refl true)
theorem decide_case : (2 : Nat) < 5 := by decide
-- cases on Or: Or.casesOn
theorem or_case (p : Prop) (h : p ∨ p) : p := by cases h with | inl hp => exact hp | inr hp => exact hp
-- cases on a structure / inductive: Nat.rec via induction
theorem ind_case (n : Nat) : 0 + n = n := by induction n with | zero => rfl | succ k ih => simp [ih]
-- let in the term
theorem let_case (n : Nat) : n = n := by let m := n; rfl
-- simp only
theorem simp_case (xs : List Nat) : (xs ++ []).length = xs.length := by simp
-- constructor (And)
theorem and_case (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩

def runHardTests : MetaM (Array String) := do
  let names : Array Name :=
    #[``rw_case, ``omega_case, ``decide_case, ``or_case,
      ``ind_case, ``let_case, ``simp_case, ``and_case]
  names.mapM testOne

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let res ← Lean.Elab.Command.liftTermElabM runHardTests
  for line in res do Lean.logInfo line

/-!
Round-trip integrity check: for each theorem, take the proof-script string,
re-parse it as a term, elaborate it against the theorem's type, and confirm it
`isDefEq`s the original proof term.
-/


/-- Parse a `by …` proof-script string, elaborate against `ty`, defeq vs `v`. -/
def roundtrips (ty v : Expr) (script : String) : MetaM Bool := do
  let env ← getEnv
  match Lean.Parser.runParserCategory env `term script with
  | .error _ => return false
  | .ok stx =>
    withoutModifyingState do
      try
        -- Turn errToSorry off so failures do not silently become `sorry`.
        let e ← TermElabM.run' (ctx := {}) <|
          withReader (fun c => { c with errToSorry := false }) do
            let e ← elabTerm stx (some ty)
            synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e
        if e.hasSorry then return false
        withNewMCtxDepth (isDefEq v e)
      catch ex =>
        if ex.isInterrupt then throw ex
        return false

/-- Reverse-elaborate, then check the rendered STRING round-trips. -/
def checkOne (n : Name) : MetaM (Name × String × Bool) := do
  let env ← getEnv
  let some ci := env.find? n | return (n, "missing", false)
  let some v := ci.value? (allowOpaque := true) | return (n, "noval", false)
  let r ← reverseProof ci.type v (enableClosers := true)
  if r.script.isEmpty then return (n, r.method, false)
  let ok ← roundtrips ci.type v r.script
  return (n, r.method, ok)

def allNames : Array Name :=
  #[``imp_self, ``imp_chain, ``refl_eq, ``all_intro, ``and_proj, ``const_fn,
  ``rw_case, ``omega_case, ``decide_case, ``or_case, ``ind_case, ``let_case,
  ``simp_case, ``and_case]

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let res ← Lean.Elab.Command.liftTermElabM
    (allNames.mapM checkOne : MetaM (Array (Name × String × Bool)))
  let mut pass := 0
  for (n, m, ok) in res do
    let mark := if ok then "OK" else "ROUNDTRIP FAIL"
    Lean.logInfo s!"{mark}  [{m}]  {n}"
    if ok then pass := pass + 1
  Lean.logInfo s!"-- round-trip: {pass}/{res.size} stored scripts re-elaborate to the original term"
