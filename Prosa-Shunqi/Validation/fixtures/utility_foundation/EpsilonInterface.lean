import Prosa.Util.Epsilon

namespace Prosa.Validation.EpsilonInterface

/-- A validation-only observable interface for the notation-only production
    module.  Its body is compiled after importing the actual production
    module, so it records the parser expansion rather than replacing it. -/
def epsilonNatValue : Nat := ε

theorem epsilonNatValue_eq_one : epsilonNatValue = 1 := by
  rfl

end Prosa.Validation.EpsilonInterface
