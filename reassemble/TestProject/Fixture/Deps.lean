-- A module with a real theorem->theorem dependency edge (`mid` uses `base`), which
-- `Fixture/Basic.lean` lacks. The reassembler's dependency-conflict detection keys on
-- exactly such edges: deleting `base` while keeping `mid` would break the build, and
-- pruning `leaf` (which nothing depends on) must not. Self-contained (no
-- project-internal import) so the test harness can elaborate it directly.
namespace Fixture.Deps

theorem base : True := by
  trivial

theorem mid : True := by
  exact base

theorem leaf : True := by
  trivial

end Fixture.Deps
