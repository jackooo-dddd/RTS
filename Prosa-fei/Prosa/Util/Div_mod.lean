-- Translated from: ../rt-proofs/util/div_mod.v
import Mathlib.Tactic
import Prosa.Util.Nat

namespace Prosa.Util.Div_mod

def div_floor (x y : ℕ) : ℕ := x / y

def div_ceil (x y : ℕ) : ℕ := if y ∣ x then x / y else x / y + 1

theorem mod_elim (a b c : ℕ) (CP : c > 0) (BC : b < c) :
    (a + c - b) % c = if a % c ≥ b then a % c - b else a % c + c - b := by
  have G : a % c < c := Nat.mod_lt a CP
  split_ifs with h
  · -- case a % c ≥ b
    have hba : b ≤ a := le_trans h (Nat.mod_le a c)
    have key : a + c - b = (a - b) + c := by omega
    rw [key, Nat.add_mod_right]
    conv_lhs => rw [show a = c * (a / c) + a % c from (Nat.div_add_mod a c).symm]
    rw [show c * (a / c) + a % c - b = c * (a / c) + (a % c - b) from by omega]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)
  · -- case a % c < b
    push_neg at h
    have key : a + c - b = a + (c - b) := by omega
    rw [key]
    conv_lhs => rw [show a = c * (a / c) + a % c from (Nat.div_add_mod a c).symm]
    rw [show c * (a / c) + a % c + (c - b) = c * (a / c) + (a % c + (c - b)) from by omega]
    rw [Nat.mul_add_mod]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

end Prosa.Util.Div_mod
