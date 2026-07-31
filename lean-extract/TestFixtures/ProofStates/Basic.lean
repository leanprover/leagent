/-
Fixture for `--proof-states` end-to-end extraction.

Each declaration here pins one behaviour of the mode, so a change in output is
attributable. Kept in `lean-extract` rather than added to
`reassemble/TestProject`, whose `records.jsonl` and byte-for-byte rewrite
comparisons would be perturbed by new declarations.
-/
namespace ProofStatesFixture

/-- Tactic proof, flat. One step, closed. -/
theorem flat : True := by
  trivial

/-- Term proof: no tactic nodes at all, so it must be COUNTED as term-proved and
never emitted as an empty row. -/
theorem termProved : 1 = 1 := rfl

/-- Nesting: `induction … with` is a parent step whose children are the
per-alternative tactics. -/
theorem nested (n : Nat) : n + 0 = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp

/-- A combinator re-running one tactic per goal: the two `simp` invocations share a
range and must merge into a single step with `invocations = 2`. -/
theorem combinator (a b : Nat) : a + 0 = a ∧ b + 0 = b := by
  refine ⟨?_, ?_⟩
  all_goals simp

/-- A `where` auxiliary carrying its own tactic proof. The auxiliary is lifted into
its own constant and must get its own record, with `parent_decl` naming this
theorem.

Deliberately shaped like the case that motivates extracting auxiliaries at all: the
parent's proof is a single `exact`, while ALL the proof work — the induction and its
cases — is in the auxiliary. Losing the aux record would mean losing the only
interesting trajectory here, so this fixture asserts the aux carries strictly more
steps than its parent. -/
theorem withAux (n : Nat) : n + 0 = n := by
  exact aux n
where
  aux : ∀ m : Nat, m + 0 = m := by
    intro m
    induction m with
    | zero => rfl
    | succ k ih => simp

/-- Two auxiliaries in one `where` clause: one tactic-proved (own record), one
term-proved (counted, not emitted). Guards against one aux overwriting the other. -/
theorem twoAuxes (n : Nat) : n + 0 = n ∧ 0 + n = n := by
  exact ⟨tac n, term n⟩
where
  tac : ∀ m : Nat, m + 0 = m := by intro m; simp
  term : ∀ m : Nat, 0 + m = m := fun m => Nat.zero_add m

/-- A `where` auxiliary on a `def`: it is not a theorem, so it must not be emitted
at all — not even as a term-proved count. -/
def defWithAux (n : Nat) : Nat := helper n + 1
where
  helper : Nat → Nat := fun k => k * 2

end ProofStatesFixture
