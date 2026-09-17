-- Translated from: ../rt-proofs/classic/util/nat.v
import Mathlib.Tactic
import Mathlib.Order.MinMax
import Prosa.Util.Nat
import Prosa.Classic.Util.Tactics

namespace Prosa.Classic.Util.Nat

section NatLemmas

lemma addnb (b1 b2 : Bool) :
    ((b1.toNat + b2.toNat) != 0) = (b1 || b2) := by
  cases b1 <;> cases b2 <;> simp

lemma subh4 (m n p : ℕ) (h1 : m ≤ n) (h2 : p ≤ n) :
    (m = n - p) ↔ (p = n - m) := by omega

lemma addmovr (m n p : ℕ) (h : m ≥ n) :
    (m - n = p ↔ m = p + n) := by omega

lemma addmovl (m n p : ℕ) (h : m ≥ n) :
    (p = m - n ↔ p + n = m) := by omega

lemma ltSnm (n m : ℕ) (h : n + 1 < m) : n < m := by omega

lemma min_lt_same (x y z : ℕ) (h : min x z < min y z) : x < y := by
  simp [Nat.min_def] at h
  split at h <;> split at h <;> omega

end NatLemmas

end Prosa.Classic.Util.Nat
