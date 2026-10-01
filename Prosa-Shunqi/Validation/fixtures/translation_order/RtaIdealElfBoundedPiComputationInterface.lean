import Prosa.Results.Rta.Ideal.Elf.BoundedPi
import Validation.fixtures.translation_order.RtaIdealGelBoundedPiComputationInterface

/-!
Export root for `results/rta/ideal/elf/bounded_pi.v`: the eleven definitions (computational) and the eleven
statements (statement-only), together with the accepted ideal GEL bounded-priority-inversion export root. Three
equations are added: the right fold defining the accepted `maxFiltered` on `[]` and on `x :: xs` (by the Boolean
value of the filter at `x`), as for the accepted `bigMaxListCond` equations; and the three constructor equations of
integer addition with a negative left operand, completing the accepted `PriorityGelInterface` equations for a
non-negative left operand.
-/

namespace Prosa.Validation.RtaIdealElfBoundedPiInterface

open Prosa.Util.Sum

universe u

theorem production_maxFiltered_nil {X : Type u} (P : X → Bool) (F : X → Nat) :
    maxFiltered [] P F = 0 := rfl

theorem production_maxFiltered_cons_true {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = true) :
    maxFiltered (x :: xs) P F = Nat.max (F x) (maxFiltered xs P F) := by
  simp [maxFiltered, h]

theorem production_maxFiltered_cons_false {X : Type u} (P : X → Bool) (F : X → Nat)
    (x : X) (xs : List X) (h : P x = false) :
    maxFiltered (x :: xs) P F = maxFiltered xs P F := by
  simp [maxFiltered, h]

theorem production_int_add_negSucc_ofNat_lt (m n : Nat) (h : m < n) :
    Int.negSucc m + Int.ofNat n = Int.ofNat (n - (m + 1)) := by
  rw [Int.negSucc_eq, Int.ofNat_eq_natCast, Int.ofNat_eq_natCast]
  omega

theorem production_int_add_negSucc_ofNat_ge (m n : Nat) (h : ¬ m < n) :
    Int.negSucc m + Int.ofNat n = Int.negSucc (m - n) := by
  rw [Int.negSucc_eq, Int.negSucc_eq, Int.ofNat_eq_natCast]
  omega

theorem production_int_add_negSucc_negSucc (m n : Nat) :
    Int.negSucc m + Int.negSucc n = Int.negSucc (m + n + 1) := by
  rw [Int.negSucc_eq, Int.negSucc_eq, Int.negSucc_eq]
  omega

end Prosa.Validation.RtaIdealElfBoundedPiInterface
