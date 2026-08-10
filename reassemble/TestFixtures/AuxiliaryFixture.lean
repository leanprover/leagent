-- Fixture for the auxiliary-record case: a theorem whose proof introduces a
-- `where`-clause helper. Lean lifts `helper` to its own constant
-- (`AuxiliaryFixture.parent.helper`) with its own declaration range, but the helper
-- has NO standalone command syntax — it lives inside `parent`'s `where` clause. The
-- reassembler must classify a record for it as `auxiliary` (excluded), not a failure:
-- holing/keeping `parent` already governs the whole proof the helper lives in.
namespace AuxiliaryFixture

theorem parent (n : Nat) : n + 0 = n := by
  exact helper n
where
  helper (m : Nat) : m + 0 = m := Nat.add_zero m

end AuxiliaryFixture
