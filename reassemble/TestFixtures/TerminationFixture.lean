-- A genuinely well-founded-recursive theorem in `:= by` (`.simple`) form carrying
-- explicit termination hints, mirroring the shape of Cedar's `ofEnv` /
-- `EnvironmentValidation` well-formedness proofs. The hints sit in a
-- `Termination.suffix` SIBLING of the proof term, so replacing only the term with a
-- hole would strand them on a body that is no longer recursive. Self-contained
-- (no project-internal import) so the harness can elaborate it directly.
--
-- The test greps the rewritten source for hint keywords and counts holes, so this
-- comment must spell out neither the hint keywords nor the hole token; they appear
-- only in the theorems below.
namespace TerminationFixture

theorem rec_le : (n : Nat) → n ≤ n := by
  intro n
  match n with
  | 0 => omega
  | k + 1 =>
    have := rec_le k
    omega
termination_by n => n
decreasing_by
  omega

-- A `mutual … end` block of mutually recursive theorems, each with its OWN termination
-- hints — the shape of Cedar's `EnvironmentValidation` well-formedness proofs. Holing
-- only SOME members changes the group's recursion and breaks the survivors' decreasing
-- proof, so the reassembler must hole every member and strip every member's hints.
mutual
theorem ping_nonneg (n : Nat) : 0 ≤ n := by
  match n with
  | 0 => omega
  | k + 1 => have := pong_nonneg k; omega
termination_by n
decreasing_by omega

theorem pong_nonneg (n : Nat) : 0 ≤ n := by
  match n with
  | 0 => omega
  | k + 1 => have := ping_nonneg k; omega
termination_by n
decreasing_by omega
end

end TerminationFixture
