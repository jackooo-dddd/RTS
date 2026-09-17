-- Translated from: ../rt-proofs/classic/util/sum.v
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Prosa.Util.Sum
import Prosa.Util.Ssromega
import Prosa.Classic.Util.Tactics
import Prosa.Classic.Util.Notation
import Prosa.Classic.Util.Sorting
import Prosa.Classic.Util.Nat

namespace Prosa.Classic.Util.Sum

section ExtraLemmas

theorem extend_sum (t1 t2 t1' t2' : ℕ) (F : ℕ → ℕ)
    (h1 : t1' ≤ t1) (h2 : t2 ≤ t2') :
    ∑ t ∈ Finset.Ico t1 t2, F t ≤ ∑ t ∈ Finset.Ico t1' t2', F t := by
  apply Finset.sum_le_sum_of_subset
  intro x hx
  rw [Finset.mem_Ico] at hx ⊢
  exact ⟨le_trans h1 hx.1, lt_of_lt_of_le hx.2 h2⟩

theorem leq_sum_nat (m n : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (E1 E2 : ℕ → ℕ)
    (h : ∀ i, m ≤ i ∧ i < n → P i → E1 i ≤ E2 i) :
    ∑ i ∈ (Finset.Ico m n).filter P, E1 i ≤
    ∑ i ∈ (Finset.Ico m n).filter P, E2 i := by
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_filter, Finset.mem_Ico] at hi
  exact h i ⟨hi.1.1, hi.1.2⟩ hi.2

theorem leq_sum1_smaller_range (m n : ℕ) (P Q : ℕ → Prop)
    [DecidablePred P] [DecidablePred Q] (a b : ℕ)
    (h : ∀ i, m ≤ i ∧ i < n ∧ P i → a ≤ i ∧ i < b ∧ Q i) :
    ((Finset.Ico m n).filter P).card ≤ ((Finset.Ico a b).filter Q).card := by
  apply Finset.card_le_card
  intro x hx
  rw [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
  have := h x ⟨hx.1.1, hx.1.2, hx.2⟩
  exact ⟨⟨this.1, this.2.1⟩, this.2.2⟩

theorem leq_pred_sum {T : Type _} [DecidableEq T] (r : List T)
    (P1 P2 : T → Bool) (F : T → ℕ)
    (h : ∀ i, P1 i → P2 i) :
    ((r.filter (fun i => P1 i)).map F).sum ≤
    ((r.filter (fun i => P2 i)).map F).sum := by
  induction r with
  | nil => simp
  | cons a t ih =>
    simp only [List.filter_cons]
    cases hP1 : P1 a <;> cases hP2 : P2 a
    · -- P1 a = false, P2 a = false
      exact ih
    · -- P1 a = false, P2 a = true
      simp only [hP1, hP2, ite_false, ite_true, List.map_cons, List.sum_cons]
      exact le_trans ih (Nat.le_add_left _ _)
    · -- P1 a = true, P2 a = false
      exfalso; have := h a (by rw [hP1]); rw [hP2] at this; exact absurd this Bool.false_ne_true
    · -- P1 a = true, P2 a = true
      simp only [hP1, hP2, ite_true, List.map_cons, List.sum_cons]
      exact Nat.add_le_add_left ih _

theorem sum_le_summation_range (f : ℕ → ℕ) (t Δ : ℕ)
    (h : ∑ x ∈ Finset.Ico t (t + Δ), f x < Δ) :
    ∃ x, t ≤ x ∧ x < t + Δ ∧ f x = 0 := by
  exact Prosa.Util.Sum.sum_le_summation_range f t Δ h

end ExtraLemmas

section SumArithmetic

theorem telescoping_sum {T : Type _} (F : T → ℕ) (r : List T) (x0 : T)
    (h : ∀ i, i < r.length - 1 →
      F (r.getD i x0) ≤ F (r.getD (i + 1) x0)) :
    F (r.getD (r.length - 1) x0) - F (r.getD 0 x0) =
    ∑ i ∈ Finset.Ico 0 (r.length - 1),
      (F (r.getD (i + 1) x0) - F (r.getD i x0)) := by
  suffices ∀ p, p ≤ r.length - 1 →
    F (r.getD p x0) - F (r.getD 0 x0) =
    ∑ i ∈ Finset.Ico 0 p, (F (r.getD (i + 1) x0) - F (r.getD i x0)) by
    exact this _ (le_refl _)
  intro p hp
  induction p with
  | zero => simp
  | succ q ihq =>
    have hq_le : q ≤ r.length - 1 := by omega
    have hq_lt : q < r.length - 1 := by omega
    have sum_split : ∑ i ∈ Finset.Ico 0 (q + 1), (F (r.getD (i + 1) x0) - F (r.getD i x0)) =
        (∑ i ∈ Finset.Ico 0 q, (F (r.getD (i + 1) x0) - F (r.getD i x0))) +
        (F (r.getD (q + 1) x0) - F (r.getD q x0)) := by
      have : Finset.Ico 0 (q + 1) = Finset.Ico 0 q ∪ {q} := by
        ext x; simp [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]; omega
      rw [this, Finset.sum_union]
      · simp
      · simp [Finset.disjoint_left]; omega
    rw [sum_split]
    have hle_q : F (r.getD q x0) ≤ F (r.getD (q + 1) x0) := h q hq_lt
    have hle_0_q : F (r.getD 0 x0) ≤ F (r.getD q x0) := by
      have := Prosa.Classic.Util.Sorting.prev_le_next F r x0 0 q (fun i hi => h i hi) (by omega)
      simpa using this
    have ihq' := ihq hq_le
    omega

theorem leq_sum_sub_uniq {T : Type _} [DecidableEq T] (r1 r2 : List T)
    (F : T → ℕ) (UNIQ : r1.Nodup) (SUB : ∀ x, x ∈ r1 → x ∈ r2) :
    (r1.map F).sum ≤ (r2.map F).sum := by
  induction r1 generalizing r2 with
  | nil => simp
  | cons x r1' ih =>
    rw [List.nodup_cons] at UNIQ
    obtain ⟨hx_notin, huniq'⟩ := UNIQ
    simp only [List.map_cons, List.sum_cons]
    have hx_in_r2 : x ∈ r2 := SUB x (by simp)
    obtain ⟨l1, l2, rfl⟩ := List.append_of_mem hx_in_r2
    simp only [List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    have hsub' : ∀ y, y ∈ r1' → y ∈ l1 ++ l2 := by
      intro y hy
      have hmem := SUB y (List.mem_cons_of_mem x hy)
      rw [List.mem_append] at hmem ⊢
      rcases hmem with h1 | h2
      · left; exact h1
      · rw [List.mem_cons] at h2
        rcases h2 with rfl | h3
        · exact absurd hy hx_notin
        · right; exact h3
    have key := ih (r2 := l1 ++ l2) huniq' hsub'
    rw [List.map_append, List.sum_append] at key
    omega

end SumArithmetic

end Prosa.Classic.Util.Sum
