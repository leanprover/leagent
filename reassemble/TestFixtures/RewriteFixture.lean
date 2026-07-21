namespace ReassemblyFixture

theorem termProof : True := True.intro

theorem tacticProof : 1 = 1 := by
  rfl

theorem equationProof : ∀ n : Nat, n = n
  | _ => rfl

theorem whereProof : True ∧ True where
  left := True.intro
  right := True.intro

theorem commentProof : True := by
  /- outer comment
     /- nested comment -/
  -/
  -- line comment
  exact True.intro

theorem unicodeProof (text : String := "λ") : True := by
  -- Unicode inside the proof: αβγ
  exact True.intro

/-- A documented theorem. -/
@[simp] theorem attributedProof : True := by
  trivial

private theorem privateProof : True := by
  exact True.intro

end ReassemblyFixture
