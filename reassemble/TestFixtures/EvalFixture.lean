-- Fixture for the eval-strip pass: one of every evaluation command the reassembler
-- removes when a proof is holed, interleaved with real declarations that must
-- survive. Everything here elaborates cleanly (no `sorry`), so the fixture can be
-- elaborated in the test and the strip logic exercised on its commands.
namespace EvalFixture

def answer : Nat := 42

#eval answer

#eval! answer

#reduce answer

#guard answer == 42

/-- info: 42 -/
#guard_msgs in
#eval answer

theorem answer_eq : answer = 42 := rfl

#check answer

end EvalFixture
