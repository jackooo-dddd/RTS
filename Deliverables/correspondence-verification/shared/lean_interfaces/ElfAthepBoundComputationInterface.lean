import Prosa.Analysis.Definitions.Workload.ElfAthepBound
import Validation.fixtures.translation_order.EdfAthepBoundComputationInterface
import Validation.fixtures.translation_order.PriorityElfComputationInterface

/-!
Export root for `analysis/definitions/workload/elf_athep_bound.v`: the four definitions together with the
accepted EDF workload-bound export root (request-bound functions, kernel-checked `min` equations) and the accepted
ELF/GEL export root (kernel-checked `Int` equations), plus eight kernel-checked `Int` constructor equations for
subtraction and for `natAbs (max 0 _)`, proved in Lean and exported with their proofs.
-/

namespace Prosa.Validation.ElfAthepBoundInterface

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

theorem production_int_natAbs_max_ofNat (n : Nat) : Int.natAbs (max 0 (Int.ofNat n)) = n := by
  rw [Int.ofNat_eq_natCast]; omega

theorem production_int_natAbs_max_negSucc (n : Nat) : Int.natAbs (max 0 (Int.negSucc n)) = 0 := by
  rw [Int.negSucc_eq]; omega

end Prosa.Validation.ElfAthepBoundInterface
