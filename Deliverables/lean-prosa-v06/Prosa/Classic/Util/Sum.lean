-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/util/sum.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 20)

import Prosa.Util.Sum
import Prosa.Classic.Util.Notation
import Prosa.Classic.Util.Sorting
import Prosa.Classic.Util.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Lemmas about sums.  The source re-exports `prosa.util.sum` (imported above) and
the Ltac-only `prosa.classic.util.ssromega` (no Lean counterpart; Lean proofs use
`omega`).

Representation notes (as in the accepted v0.6 translation):
* `\sum_(i <- r) F i` is `Prosa.Util.Sum.sumSeq r F` and
  `\sum_(i <- r | P i) F i` is `Prosa.Util.Sum.sumFiltered r P F`;
* `\sum_(m <= i < n) F i` is `∑ i ∈ Finset.Ico m n, F i`, and
  `\sum_(m <= i < n | P i) F i` is `∑ i ∈ (Finset.Ico m n).filter (P · = true), F i`;
* a Boolean chain `m <= i < n` in proposition position is
  `(decide (m ≤ i) && decide (i < n)) = true`; `nth x0 r i` is
  `r.getD i x0`; `{subset r1 <= r2}` is `∀ x, x ∈ r1 → x ∈ r2`.
-/

namespace Prosa.Classic.Util.Sum

open Prosa.Util.Sum
open Prosa.Classic.Util.Sorting (prev_le_next)

universe u

theorem sum_seq_diff :
    ∀ (T : Type u) [DecidableEq T] (rs : List T) (F G : T → Nat),
      (∀ i : T, i ∈ rs → G i ≤ F i) →
      sumSeq rs (fun i => F i - G i) = sumSeq rs F - sumSeq rs G := by
  intro T _ rs F G H
  induction rs with
  | nil => simp [sumSeq]
  | cons a rs ih =>
      have ih' := ih (fun i hi => H i (List.mem_cons_of_mem _ hi))
      have hle : sumSeq rs G ≤ sumSeq rs F :=
        List.sum_le_sum (fun i hi => H i (List.mem_cons_of_mem _ hi))
      have ha := H a List.mem_cons_self
      simp only [sumSeq, List.map_cons, List.sum_cons] at ih' hle ⊢
      omega

theorem sum_diff :
    ∀ (n : Nat) (F G : Nat → Nat),
      (∀ i, i < n → G i ≤ F i) →
      ∑ i ∈ Finset.Ico 0 n, (F i - G i) =
        (∑ i ∈ Finset.Ico 0 n, F i) - (∑ i ∈ Finset.Ico 0 n, G i) := by
  intro n F G ALL
  apply Finset.sum_tsub_distrib
  intro i hi
  exact ALL i (Finset.mem_Ico.mp hi).2

theorem extend_sum :
    ∀ (t1 t2 t1' t2' : Nat) (F : Nat → Nat),
      t1' ≤ t1 →
      t2 ≤ t2' →
      ∑ t ∈ Finset.Ico t1 t2, F t ≤ ∑ t ∈ Finset.Ico t1' t2', F t := by
  intro t1 t2 t1' t2' F LE1 LE2
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico LE1 LE2)

theorem leq_sum_nat (m n : Nat) (P : Nat → Bool) (E1 E2 : Nat → Nat) :
    (∀ i, (decide (m ≤ i) && decide (i < n)) = true → P i = true → E1 i ≤ E2 i) →
    ∑ i ∈ (Finset.Ico m n).filter (fun i => P i = true), E1 i ≤
      ∑ i ∈ (Finset.Ico m n).filter (fun i => P i = true), E2 i := by
  intro LE
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_filter, Finset.mem_Ico] at hi
  exact LE i (by simp [hi.1.1, hi.1.2]) hi.2

theorem leq_sum1_smaller_range (m n : Nat) (P Q : Nat → Bool) (a b : Nat) :
    (∀ i, (decide (m ≤ i) && decide (i < n)) = true ∧ P i = true →
      (decide (a ≤ i) && decide (i < b)) = true ∧ Q i = true) →
    ∑ i ∈ (Finset.Ico m n).filter (fun i => P i = true), (1 : Nat) ≤
      ∑ i ∈ (Finset.Ico a b).filter (fun i => Q i = true), (1 : Nat) := by
  intro REDUCE
  simp only [Finset.sum_const, smul_eq_mul, Nat.mul_one]
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
  have h := REDUCE i ⟨by simp [hi.1.1, hi.1.2], hi.2⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1, h.2⟩

theorem leq_pred_sum :
    ∀ (T : Type u) [DecidableEq T] (r : List T) (P1 P2 : T → Bool) (F : T → Nat),
      (∀ i, P1 i = true → P2 i = true) →
      sumFiltered r P1 F ≤ sumFiltered r P2 F := by
  intro T _ r P1 P2 F H
  induction r with
  | nil => simp [sumFiltered]
  | cons a r ih =>
      simp only [sumFiltered, List.filter_cons] at ih ⊢
      by_cases h1 : P1 a = true
      · simp [h1, H a h1]; omega
      · have h1' : P1 a = false := by simpa using h1
        simp only [h1', Bool.false_eq_true, ↓reduceIte]
        split
        · simp; omega
        · exact ih

theorem sum_le_summation_range :
    ∀ (f : Nat → Nat) (t Δ : Nat),
      ∑ x ∈ Finset.Ico t (t + Δ), f x < Δ →
      ∃ x, (decide (t ≤ x) && decide (x < t + Δ)) = true ∧ f x = 0 := by
  intro f t Δ H
  obtain ⟨x, h1, h2, h3⟩ := Prosa.Util.Sum.sum_le_summation_range f t Δ H
  exact ⟨x, by simp [h1, h2], h3⟩

theorem telescoping_sum :
    ∀ (T : Type u) (F : T → Nat) (r : List T) (x0 : T),
      (∀ i, i < r.length - 1 → F (r.getD i x0) ≤ F (r.getD (i + 1) x0)) →
      F (r.getD (r.length - 1) x0) - F (r.getD 0 x0) =
        ∑ i ∈ Finset.Ico 0 (r.length - 1), (F (r.getD (i + 1) x0) - F (r.getD i x0)) := by
  intro T F r x0 ALL
  have key : ∀ m, m ≤ r.length - 1 →
      F (r.getD m x0) - F (r.getD 0 x0) =
        ∑ i ∈ Finset.Ico 0 m, (F (r.getD (i + 1) x0) - F (r.getD i x0)) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
        intro hm
        rw [Finset.sum_Ico_succ_top (Nat.zero_le m), ← ih (by omega)]
        have h0 : F (r.getD 0 x0) ≤ F (r.getD m x0) := by
          simpa using prev_le_next F r x0 0 m ALL (by omega)
        have h1 := ALL m (by omega)
        omega
  exact key _ (Nat.le_refl _)

theorem leq_sum_sub_uniq :
    ∀ (T : Type u) [DecidableEq T] (r1 r2 : List T) (F : T → Nat),
      r1.Nodup →
      (∀ x, x ∈ r1 → x ∈ r2) →
      sumSeq r1 F ≤ sumSeq r2 F := by
  intro T _ r1 r2 F UNIQ SUB
  exact Prosa.Util.Sum.leq_sum_sub_uniq r1 F r2 UNIQ SUB

end Prosa.Classic.Util.Sum
