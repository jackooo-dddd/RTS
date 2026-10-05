import Prosa.Results.Rta.Ideal.Gel.BoundedPi
import Validation.fixtures.translation_order.RtaIdealEdfBoundedNpsComputationInterface
import Validation.fixtures.translation_order.ElfAthepBoundComputationInterface

/-!
Export root for `results/rta/ideal/gel/bounded_pi.v`: the four definitions (computational) and the six
statements (statement-only), together with the accepted ideal EDF bounded-nonpreemptive-segments export root and the
accepted GEL / ELF-athep-bound interface roots (their integer addition, order, subtraction and `natAbs (max 0 _)`
equations). One integer equation is added: `decide (a ≠ b)` on `Int` by the two order tests (the same statement and
proof as the accepted `SearchSpaceElfInterface.production_int_decide_ne`).
-/

namespace Prosa.Validation.RtaIdealGelBoundedPiInterface

theorem production_int_decide_ne (a b : Int) :
    decide (a ≠ b) = !(decide (a ≤ b) && decide (b ≤ a)) := by
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (a ≤ b ∧ b ≤ a) := fun ⟨h1, h2⟩ => h (Int.le_antisymm h1 h2)
    simp only [Bool.not_and]
    by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a <;> simp_all

end Prosa.Validation.RtaIdealGelBoundedPiInterface
