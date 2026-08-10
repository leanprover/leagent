-- A record-free module (no theorems, so the reassembler never rewrites it) that
-- nonetheless carries evaluation commands. It exercises the eval-strip pass's
-- SECOND pass, which visits files the theorem loop skipped. See `materializeRepo`.
-- Self-contained (no project-internal import) so the test harness, which elaborates
-- it directly rather than under `lake env`, can resolve it.
namespace Fixture.Examples

def sample : Nat := 7

#eval sample

/-- info: 7 -/
#guard_msgs in
#eval sample

#guard sample == 7

end Fixture.Examples
