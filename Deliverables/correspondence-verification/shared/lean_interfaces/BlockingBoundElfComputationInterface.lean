import Prosa.Analysis.Definitions.BlockingBound.Elf
import Validation.fixtures.translation_order.BlockingBoundFpComputationInterface
import Validation.fixtures.translation_order.PriorityElfComputationInterface

/-!
Export root for `analysis/definitions/blocking_bound/elf.v`: the ELF blocking bound together with the
accepted blocking-bound export root (with its kernel-checked conditional-maximum equations) and the accepted
ELF/GEL export root (with its kernel-checked `Int` equations), plus one kernel-checked `Int` order equation
for the strict comparison of a shifted priority point, proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.BlockingBoundElfInterface

/-- Kernel-checked `Int` order equation for the strict comparison of a shifted priority point (proved in
Lean, exported with its proof). -/
theorem production_int_add_lt_iff (A : Nat) (p q : Int) :
    decide ((A : Int) + p < q) = decide (((A + 1 : Nat) : Int) + p ≤ q) := by
  simp only [decide_eq_decide]
  constructor <;> intro h <;> omega

end Prosa.Validation.BlockingBoundElfInterface
