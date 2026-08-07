import Corpus.ProofMetrics
import Corpus.CollectCommon
import Corpus.TestAssert

/-!
Tests for `--proof-metrics` (`Corpus.ProofMetrics`).

The analysis is a pure function over declaration `Syntax`, so each test parses one
declaration against a real `Init` environment (needed only so the tactic parser
category is populated — the same reason `ProofStatesTests.testCategoryFilter` builds
an environment) and asserts the metrics it yields. This exercises the classifiers
(case-split / rewrite / have / automation), the term-vs-tactic split, nesting depth,
`calc`-step counting, and attribute harvesting against syntax the parser actually
produces, rather than hand-built trees that could drift from real node shapes.
-/

open Lean
open Corpus
open Corpus.ProofMetrics

namespace ProofMetricsTests

open Corpus.TestAssert (assert)

/-- Parse one top-level command and compute its metrics against `env`. -/
private def metricsOf (env : Environment) (src : String) : Except String TacticMetrics :=
  match Lean.Parser.runParserCategory env `command src with
  | .error e => .error s!"parse failed for {src}: {e}"
  | .ok stx  => .ok (metricsForCommand (CollectCommon.tacticKindSet env) stx)

private def testTermProof (env : Environment) : IO Unit := do
  let m ← IO.ofExcept <| metricsOf env "theorem foo : True := True.intro"
  assert m.isTermProof "term proof not flagged as term"
  assert (m.tacticStepCount == none) "term proof has a tactic step count"
  assert (m.tacticTotalCount == none) "term proof has a tactic total"
  assert (m.maxTacticDepth == none) "term proof has a depth"
  assert m.tacticKinds.isEmpty "term proof has tactic kinds"
  assert (m.caseSplitCount == none) "term proof has a case-split count"
  assert m.automationTactics.isEmpty "term proof has automation tactics"

private def testFlatTacticProof (env : Environment) : IO Unit := do
  -- Two flat top-level tactics, no nesting.
  let m ← IO.ofExcept <| metricsOf env "theorem foo : True := by simp; trivial"
  assert (!m.isTermProof) "tactic proof flagged as term"
  assert (m.tacticStepCount == some 2) s!"top-level step count wrong: {m.tacticStepCount}"
  assert (m.maxTacticDepth == some 0) s!"flat proof has nonzero depth: {m.maxTacticDepth}"
  assert (m.automationTactics == #["simp"]) s!"automation set wrong: {m.automationTactics}"

private def testNestingAndCombinator (env : Environment) : IO Unit := do
  -- `<;>` is itself a tactic-category node, so its operands nest one level under it.
  let m ← IO.ofExcept <| metricsOf env "theorem foo : True := by (simp <;> trivial)"
  assert (m.maxTacticDepth.getD 0 ≥ 1)
    s!"combinator did not nest its operands: {m.maxTacticDepth}"
  assert (m.tacticTotalCount.getD 0 ≥ 3)
    s!"combinator + operands undercounted: {m.tacticTotalCount}"

private def testCaseSplitRewriteHave (env : Environment) : IO Unit := do
  let m ← IO.ofExcept <| metricsOf env
    "theorem foo (h : 0 = 0) : True := by cases h; rw [Nat.add_comm]; have x := h; trivial"
  assert (m.caseSplitCount == some 1) s!"case split miscounted: {m.caseSplitCount}"
  assert (m.rewriteCount == some 1) s!"rewrite miscounted: {m.rewriteCount}"
  assert (m.haveCount == some 1) s!"have miscounted: {m.haveCount}"
  -- `simp`/`simp_all` are automation, NOT rewrites — guard the boundary.
  let m2 ← IO.ofExcept <| metricsOf env "theorem bar : True := by simp"
  assert (m2.rewriteCount == some 0) s!"simp counted as a rewrite: {m2.rewriteCount}"
  assert (m2.automationTactics == #["simp"]) s!"simp not classed as automation: {m2.automationTactics}"

private def testCalcSteps (env : Environment) : IO Unit := do
  -- A `calc` with two steps after the first relation.
  let src := "theorem foo : 1 = 1 := by calc 1 = 1 := rfl\n  _ = 1 := rfl\n  _ = 1 := rfl"
  let m ← IO.ofExcept <| metricsOf env src
  assert (m.calcSteps == some 2) s!"calc steps wrong (want 2 non-first steps): {m.calcSteps}"

private def testHistogram (env : Environment) : IO Unit := do
  let m ← IO.ofExcept <| metricsOf env "theorem foo : True := by simp; simp; trivial"
  let simpKind := toString ``Lean.Parser.Tactic.simp
  let count := (m.tacticHistogram.find? (·.1 == simpKind)).map (·.2)
  assert (count == some 2) s!"histogram miscounted simp: {m.tacticHistogram}"
  -- `tacticKinds` is the deduped, sorted key set of the histogram.
  assert (m.tacticKinds == (m.tacticHistogram.map (·.1)).qsort (· < ·))
    s!"tacticKinds disagrees with histogram keys: {m.tacticKinds}"

private def testAttributes (env : Environment) : IO Unit := do
  let m ← IO.ofExcept <| metricsOf env "@[simp, reducible] theorem foo : True := by trivial"
  assert (m.attributes == #["reducible", "simp"])
    s!"attributes wrong (want sorted [reducible, simp]): {m.attributes}"
  -- No attributes → empty, on a term proof too.
  let m2 ← IO.ofExcept <| metricsOf env "def d : Nat := 0"
  assert m2.attributes.isEmpty s!"spurious attributes: {m2.attributes}"
  assert m2.isTermProof "a plain def value is a term, not a tactic proof"

unsafe def run : IO UInt32 := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Init }] {} (trustLevel := 1024) (loadExts := true)
  testTermProof env
  testFlatTacticProof env
  testNestingAndCombinator env
  testCaseSplitRewriteHave env
  testCalcSteps env
  testHistogram env
  testAttributes env
  IO.println "proof metrics tests passed"
  return (0 : UInt32)

end ProofMetricsTests

unsafe def main : IO UInt32 := ProofMetricsTests.run
