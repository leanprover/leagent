import Lean
import WorkerPlugins.GrindManifest

/-!
Smoke test for `WorkerPlugins.GrindManifest`: run grind's default strategy on a
handful of grind-provable goals via the SAME Meta-level pipeline the plugin uses,
and print the interactive script, the `grind only` reconstruction, and the
available/activated/used triple. This is not an assertion suite — it exists to
eyeball that the extracted artifacts look sensible (and how anchor-heavy the
interactive scripts are on real proofs).
-/

namespace WorkerPlugins.Test.Grind
open Lean Lean.Meta Lean.Meta.Grind

-- Some goals grind should close, spanning a few "move" kinds.
theorem t_refl (a : Nat) : a = a := rfl
theorem t_comm_add (a b : Nat) : a + b = b + a := by grind
theorem t_and (p q : Prop) (h : p ∧ q) : q ∧ p := by grind
theorem t_ite (p : Prop) [Decidable p] (a : Nat) :
    (if p then a else a) = a := by grind
theorem t_cases (p q : Prop) (h : p ∨ q) (hp : p → q) (_hq : q → q) : q := by grind

/-- A function grind will NOT unfold on its own + a tagged rewrite lemma, so we
can see the hint appear in `available` and — when the proof genuinely
instantiates it — in `activated`/`used`. The LHS `foo (n+1)` stays a stable
E-matching pattern (grind does not unfold plain defs). -/
def foo (n : Nat) : Nat := n * 2 + 1
@[grind =] theorem foo_eq (n : Nat) : foo (n + 1) = foo n + 2 := by
  unfold foo; omega

theorem t_uses_hint (n : Nat) : foo (n + 1) = foo n + 2 := by grind

/-- Reflect over the theorems declared here and run the grind pipeline on each,
using the plugin's own public tester. -/
def runTests : MetaM (Array String) := do
  let names : Array Name :=
    #[``t_refl, ``t_comm_add, ``t_and, ``t_ite, ``t_cases, ``t_uses_hint]
  let env ← getEnv
  let available := WorkerPlugins.GrindManifest.availableHintsPublic env
  let mut out : Array String := #[s!"AVAILABLE ({available.size}): {available.toList}"]
  for n in names do
    let some ci := env.find? n | continue
    let e ← WorkerPlugins.GrindManifest.runGrindOnPublic ci.type
    out := out.push <|
      s!"━━ {n}\n" ++
      s!"   goal:        {e.goalType}\n" ++
      s!"   outcome:     {e.outcome}\n" ++
      s!"   interactive: {e.interactive}\n" ++
      s!"   grind_only:  {e.grindOnly}\n" ++
      s!"   activated:   {e.activated.toList}\n" ++
      s!"   used:        {e.used.toList}\n" ++
      s!"   coverageGap: {e.coverageGap}"
  return out

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let res ← Lean.Elab.Command.liftTermElabM runTests
  for line in res do
    Lean.logInfo line

end WorkerPlugins.Test.Grind
