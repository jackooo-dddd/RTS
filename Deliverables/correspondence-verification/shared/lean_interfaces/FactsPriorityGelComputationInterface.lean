import Prosa.Analysis.Facts.Priority.Gel
import Validation.fixtures.translation_order.FactsPreemptionComputationInterface
import Validation.fixtures.translation_order.PriorityGelComputationInterface

/-!
Export root for `analysis/facts/priority/gel.v`: the six statements together with the accepted
preemption-facts export root and the accepted GEL export root (with its kernel-checked `Int` constructor
equations), plus two kernel-checked `Int` order equations for differences, proved in Lean and exported with
their proofs.
-/

namespace Prosa.Validation.FactsPriorityGelInterface

/-- Kernel-checked `Int` order equation for a difference (proved in Lean, exported with its proof). -/
theorem production_int_le_sub_iff (a b c : Int) : decide (a ≤ b - c) = decide (a + c ≤ b) := by
  simp only [decide_eq_decide]
  constructor <;> intro h <;> omega

/-- Kernel-checked `Int` order equation for a nonnegative difference (proved in Lean, exported with its proof). -/
theorem production_int_zero_le_sub_iff (b c : Int) : decide (0 ≤ b - c) = decide (c ≤ b) := by
  simp only [decide_eq_decide]
  constructor <;> intro h <;> omega

end Prosa.Validation.FactsPriorityGelInterface
