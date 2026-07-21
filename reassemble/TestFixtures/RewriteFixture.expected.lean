namespace ReassemblyFixture

theorem termProof : True := by
  sorry

theorem tacticProof : 1 = 1 := by
  sorry

theorem equationProof : ∀ n : Nat, n = n
  := by
  sorry

theorem whereProof : True ∧ True := by
  sorry

theorem commentProof : True := by
  sorry

theorem unicodeProof (text : String := "λ") : True := by
  sorry

/-- A documented theorem. -/
@[simp] theorem attributedProof : True := by
  sorry

private theorem privateProof : True := by
  sorry

end ReassemblyFixture
