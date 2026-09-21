-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/sum.v

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Prosa.Util.Notation
import Prosa.Util.Rel
import Prosa.Util.Nat

namespace Prosa.Util.Sum

open scoped BigOperators

/-- The sum of `Delta` ones over the half-open interval `[t, t + Delta)`. -/
theorem sum_of_ones (t Δ : Nat) :
    ∑ x ∈ Finset.Ico t (t + Δ), (1 : Nat) = Δ := by
  simp

/-- A finite natural-number interval sum is zero exactly when all terms are zero. -/
theorem big_nat_eq0 (m n : Nat) (F : Nat → Nat) :
    (∑ i ∈ Finset.Ico m n, F i) = 0 ↔
      ∀ i, m ≤ i ∧ i < n → F i = 0 := by
  constructor
  · intro hsum i hi
    exact Finset.sum_eq_zero_iff.mp hsum i (Finset.mem_Ico.mpr hi)
  · intro hall
    apply Finset.sum_eq_zero
    intro i hi
    exact hall i (Finset.mem_Ico.mp hi)

/-- If an interval sum is smaller than the interval length, one term is zero. -/
theorem sum_le_summation_range (f : Nat → Nat) (t Δ : Nat)
    (h : (∑ x ∈ Finset.Ico t (t + Δ), f x) < Δ) :
    ∃ x, t ≤ x ∧ x < t + Δ ∧ f x = 0 := by
  by_contra hall
  push_neg at hall
  have hle : Δ ≤ ∑ x ∈ Finset.Ico t (t + Δ), f x := by
    calc
      Δ = ∑ _x ∈ Finset.Ico t (t + Δ), (1 : Nat) :=
        (sum_of_ones t Δ).symm
      _ ≤ ∑ x ∈ Finset.Ico t (t + Δ), f x := by
        apply Finset.sum_le_sum
        intro i hi
        have hirange := Finset.mem_Ico.mp hi
        have hne := hall i hirange.1 hirange.2
        omega
  omega

end Prosa.Util.Sum
