import Prosa.Results.Generality.Gel
import Validation.fixtures.translation_order.GeneralityElfComputationInterface

/-!
Export root for `results/generality/gel.v`: the definition and the four statements together with the
accepted ELF-generality export root (GEL/ELF policies, preemption facts, priority-driven schedules), the accepted
EDF and FIFO policies and task deadlines (reached through the statements) and kernel-checked `Int` equations
(subtraction and `natAbs` on constructors, the literal zero). Every equation is proved in Lean and exported with
its proof.
-/

namespace Prosa.Validation.GeneralityGelInterface

theorem production_int_sub_ofNat_ofNat_le (m n : Nat) (h : n ≤ m) :
    Int.ofNat m - Int.ofNat n = Int.ofNat (m - n) := by
  rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]; omega

theorem production_int_sub_ofNat_ofNat_gt (m n : Nat) (h : ¬ n ≤ m) :
    Int.ofNat m - Int.ofNat n = Int.negSucc (n - m - 1) := by
  rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]; omega

theorem production_int_sub_ofNat_negSucc (m n : Nat) :
    Int.ofNat m - Int.negSucc n = Int.ofNat (m + n + 1) := by
  rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]; omega

theorem production_int_sub_negSucc_ofNat (m n : Nat) :
    Int.negSucc m - Int.ofNat n = Int.negSucc (m + n) := by
  rw [Int.negSucc_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega

theorem production_int_sub_negSucc_negSucc_le (m n : Nat) (h : m ≤ n) :
    Int.negSucc m - Int.negSucc n = Int.ofNat (n - m) := by
  rw [Int.negSucc_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]; omega

theorem production_int_sub_negSucc_negSucc_gt (m n : Nat) (h : ¬ m ≤ n) :
    Int.negSucc m - Int.negSucc n = Int.negSucc (m - n - 1) := by
  rw [Int.negSucc_eq, Int.negSucc_eq, Int.negSucc_eq]; omega

theorem production_int_natAbs_ofNat (n : Nat) : Int.natAbs (Int.ofNat n) = n := rfl

theorem production_int_natAbs_negSucc (n : Nat) : Int.natAbs (Int.negSucc n) = n + 1 := rfl

theorem production_int_zero_eq : (0 : Int) = Int.ofNat 0 := rfl

end Prosa.Validation.GeneralityGelInterface
