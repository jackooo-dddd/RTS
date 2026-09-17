-- Translated from: ../rt-proofs/util/nat.v
import Mathlib.Tactic
import Prosa.Util.Tactics

namespace Prosa.Util.Nat

section NatLemmas

theorem subh1 (m n p : ℕ) (h : m ≥ n) : m - n + p = m + p - n := by omega

theorem subh2 (m1 m2 n1 n2 : ℕ) (h1 : m1 ≥ m2) (h2 : n1 ≥ n2) :
    (m1 + n1) - (m2 + n2) = m1 - m2 + (n1 - n2) := by omega

theorem subh3 (m n p : ℕ) (h : m + p ≤ n) : m ≤ n - p := by omega

theorem subn_abba (n a b : ℕ) (h : n ≥ b) : n + a - b + b - a = n := by omega

theorem add_subC (a b c : ℕ) (h1 : a ≥ c) (h2 : b ≥ c) :
    a + (b - c) = a - c + b := by omega

theorem ltn_subLR (a b c : ℕ) (h : a - c < b) : a < b + c := by omega

theorem leq_addk (m n k : ℕ) (h : n + k ≤ m) : n ≤ m := by omega

end NatLemmas

section Interval

theorem point_not_in_interval (t1 t2 t' : ℕ) (EXCLUDED : t2 ≤ t' ∨ t' < t1)
    (t : ℕ) (h : t1 ≤ t ∧ t < t2) : t ≠ t' := by omega

end Interval

section NatOrderLemmas

theorem ltn_leq_trans {n m p : ℕ} (h1 : m < n) (h2 : n ≤ p) : m < p := by omega

end NatOrderLemmas

end Prosa.Util.Nat
