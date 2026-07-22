namespace Fixture

def preserved : Nat := 7

theorem first : True := by
  trivial

theorem second : preserved = 7 := rfl

end Fixture
