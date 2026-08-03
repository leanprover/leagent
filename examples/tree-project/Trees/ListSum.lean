/-!
# Summing a list

A second independent base file: our own `sumList` plus the two lemmas about it
that the tree proofs need. Kept project-local on purpose, so the dependency
closure of a theorem is made of records rather than of library imports.
-/

namespace Trees

/-- Sum of a list of naturals. -/
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- `sumList` is additive over `++`. -/
theorem sumList_append (xs ys : List Nat) :
    sumList (xs ++ ys) = sumList xs + sumList ys := by
  induction xs with
  | nil => simp [sumList]
  | cons x xs ih =>
    simp [sumList, ih]
    omega

/-- Summing is insensitive to order — at least to reversal. -/
theorem sumList_reverse (xs : List Nat) : sumList xs.reverse = sumList xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [List.reverse_cons, sumList_append, sumList, ih]
    omega

end Trees
