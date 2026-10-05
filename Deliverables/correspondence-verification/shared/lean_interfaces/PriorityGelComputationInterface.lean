import Prosa.Model.Priority.Gel

/-!
Export root for `model/priority/gel.v`: the production declarations and
kernel-checked constructor equations for the `Int` operations occurring in
the GEL priority point (addition of a natural number and an integer) and in
the GEL order (the decided `≤` on `Int`).  Every equation is proved in Lean
and exported with its proof.
-/

namespace Prosa.Validation.PriorityGelInterface

theorem production_int_add_ofNat_ofNat (m n : Nat) :
    Int.ofNat m + Int.ofNat n = Int.ofNat (m + n) := rfl

theorem production_int_add_ofNat_negSucc_lt (m n : Nat) (h : n < m) :
    Int.ofNat m + Int.negSucc n = Int.ofNat (m - (n + 1)) := by
  rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
  omega

theorem production_int_add_ofNat_negSucc_ge (m n : Nat) (h : ¬ n < m) :
    Int.ofNat m + Int.negSucc n = Int.negSucc (n - m) := by
  rw [Int.negSucc_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
  omega

theorem production_int_le_ofNat_ofNat (m n : Nat) :
    decide (Int.ofNat m ≤ Int.ofNat n) = decide (m ≤ n) := by
  rw [Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
  simp only [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem production_int_le_negSucc_negSucc (m n : Nat) :
    decide (Int.negSucc m ≤ Int.negSucc n) = decide (n ≤ m) := by
  rw [Int.negSucc_eq, Int.negSucc_eq]
  simp only [decide_eq_decide]
  constructor <;> intro h <;> omega

theorem production_int_le_ofNat_negSucc (m n : Nat) :
    decide (Int.ofNat m ≤ Int.negSucc n) = false := by
  rw [Int.negSucc_eq, Int.ofNat_eq_natCast]
  simp only [decide_eq_false_iff_not]
  omega

theorem production_int_le_negSucc_ofNat (m n : Nat) :
    decide (Int.negSucc m ≤ Int.ofNat n) = true := by
  rw [Int.negSucc_eq, Int.ofNat_eq_natCast]
  simp only [decide_eq_true_eq]
  omega

theorem production_nat_cast_eq (n : Nat) : (n : Int) = Int.ofNat n := rfl

end Prosa.Validation.PriorityGelInterface
