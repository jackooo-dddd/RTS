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

/-!
The following declarations are Lean-side representation helpers.  They
are not additional Prosa source declarations.  They expose the exact
computations used by the source big operators so that the source distinctions
between sequence sums, filtered sequence sums, maxima, and Boolean
subsequence tests remain visible to semantic validation.
-/

/-- Sum a function over an ordered sequence, retaining multiplicities. -/
def sumSeq {I : Type _} (r : List I) (F : I → Nat) : Nat :=
  (r.map F).sum

/-- Sum a function over the elements satisfying a Boolean predicate. -/
def sumFiltered {I : Type _} (r : List I) (P : I → Bool)
    (F : I → Nat) : Nat :=
  ((r.filter P).map F).sum

/-- Maximum over a filtered sequence, with the source default value zero. -/
def maxFiltered {I : Type _} (r : List I) (P : I → Bool)
    (F : I → Nat) : Nat :=
  ((r.filter P).map F).foldr max 0

/-- Boolean subsequence test matching MathComp's left-to-right computation. -/
def subseqb {I : Type _} [DecidableEq I] (xs : List I) : List I → Bool
  | [] => xs.isEmpty
  | y :: ys =>
      match xs with
      | [] => true
      | x :: xs' => if x = y then subseqb xs' ys else subseqb xs ys

/-- Sum the contribution of all items in `xs` belonging to one partition. -/
def sumOfPartition {X Y : Type _} [DecidableEq Y]
    (xToY : X → Y) (f : X → Nat) (P : X → Bool)
    (xs : List X) (y : Y) : Nat :=
  sumFiltered xs (fun x => P x && decide (xToY x = y)) f

/-- Sum the item contributions partition by partition, retaining `ys` multiplicity. -/
def sumOverPartitions {X Y : Type _} [DecidableEq Y]
    (xToY : X → Y) (f : X → Nat) (P : X → Bool)
    (xs : List X) (ys : List Y) : Nat :=
  sumSeq ys (sumOfPartition xToY f P xs)

/-- A filtered sequence sum is zero exactly when every retained term is zero. -/
theorem sum_nat_eq0_nat {I : Type _} [DecidableEq I]
    (r : List I) (P : I → Bool) (F : I → Nat) :
    decide (sumFiltered r P F = 0) =
      r.all (fun x => !P x || decide (F x = 0)) := by
  induction r with
  | nil => simp [sumFiltered]
  | cons a r ih =>
      unfold sumFiltered at ih
      cases hP : P a <;> simp [sumFiltered, hP, ih]

/-- A filtered sequence sum is positive exactly when some retained term is positive. -/
theorem sum_nat_gt0 {I : Type _} [DecidableEq I]
    (r : List I) (P : I → Bool) (F : I → Nat) :
    decide (0 < sumFiltered r P F) =
      r.any (fun x => P x && decide (0 < F x)) := by
  induction r with
  | nil => simp [sumFiltered]
  | cons a r ih =>
      unfold sumFiltered at ih
      cases hP : P a <;> simp [sumFiltered, hP, ih, Nat.add_pos_iff_pos_or_pos]

/-- A pointwise constant bound gives a bound on the filtered sequence sum. -/
theorem sum_majorant_constant {I : Type _} [DecidableEq I]
    (r : List I) (P : I → Bool) (F : I → Nat) (c : Nat)
    (h : ∀ a, a ∈ r → P a = true → F a ≤ c) :
    sumFiltered r P F ≤ c * (r.filter P).length := by
  induction r with
  | nil => simp [sumFiltered]
  | cons a r ih =>
      cases hP : P a with
      | false =>
          simpa [sumFiltered, hP] using
            ih (fun x hx hPx => h x (List.mem_cons_of_mem a hx) hPx)
      | true =>
          have ha := h a List.mem_cons_self hP
          have hr := ih (fun x hx hPx => h x (List.mem_cons_of_mem a hx) hPx)
          unfold sumFiltered at hr
          simp only [sumFiltered, List.filter_cons, hP, Bool.true_eq,
            ite_true, List.map_cons, List.sum_cons, List.length_cons,
            Nat.mul_succ]
          omega

/-- Split a filtered sum across exhaustive, mutually exclusive predicates. -/
theorem sum_split_exhaustive_mutually_exclusive_preds
    {I : Type _} [DecidableEq I]
    (r : List I) (P : I → Bool) (F : I → Nat) (Q R : I → Bool)
    (hexhaustive : ∀ x, P x = (Q x || R x))
    (hexclusive : ∀ x, !(Q x && R x) = true) :
    sumFiltered r P F = sumFiltered r Q F + sumFiltered r R F := by
  induction r with
  | nil => simp [sumFiltered]
  | cons a r ih =>
      have hx := hexhaustive a
      have hn := hexclusive a
      cases hP : P a <;> cases hQ : Q a <;> cases hR : R a <;>
        simp_all [sumFiltered, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- The maximum retained value is bounded by the corresponding sum. -/
theorem bigmax_leq_sum {I : Type _} [DecidableEq I]
    (r : List I) (P : I → Bool) (F : I → Nat) :
    maxFiltered r P F ≤ sumFiltered r P F := by
  induction r with
  | nil => simp [maxFiltered, sumFiltered]
  | cons a r ih =>
      cases hP : P a with
      | false => simpa [maxFiltered, sumFiltered, hP] using ih
      | true =>
          unfold maxFiltered sumFiltered at ih
          simp only [maxFiltered, sumFiltered, List.filter_cons, hP,
            Bool.true_eq, ite_true, List.map_cons, List.foldr_cons,
            List.sum_cons]
          apply max_le
          · omega
          · exact le_trans ih (Nat.le_add_left _ _)

/-- A Boolean subsequence has no greater filtered natural-number sum. -/
theorem sum_le_subseq {I : Type _} [DecidableEq I]
    (P : I → Bool) (F : I → Nat) (r1 r2 : List I)
    (hsub : subseqb r1 r2 = true) :
    sumFiltered r1 P F ≤ sumFiltered r2 P F := by
  induction r2 generalizing r1 with
  | nil =>
      cases r1 <;> simp [subseqb, sumFiltered] at hsub ⊢
  | cons b r2 ih =>
      cases r1 with
      | nil => simp [sumFiltered]
      | cons a r1 =>
          simp only [subseqb] at hsub
          split at hsub
          · case isTrue hab =>
              subst b
              have htail := ih (r1 := r1) hsub
              cases hP : P a with
              | false => simpa [sumFiltered, hP] using htail
              | true =>
                  simpa [sumFiltered, hP] using
                    Nat.add_le_add_left htail (F a)
          · case isFalse hab =>
              have hwhole := ih (r1 := a :: r1) hsub
              cases hP : P b with
              | false => simpa [sumFiltered, hP] using hwhole
              | true =>
                  have hadd := le_trans hwhole
                    (Nat.le_add_left (sumFiltered r2 P F) (F b))
                  simpa [sumFiltered, hP] using hadd

/-- Pointwise domination is preserved by filtered sequence summation. -/
theorem leq_sum_seq {I : Type _} [DecidableEq I]
    (r : List I) (P : I → Bool) (E1 E2 : I → Nat)
    (h : ∀ i, i ∈ r → P i = true → E1 i ≤ E2 i) :
    sumFiltered r P E1 ≤ sumFiltered r P E2 := by
  induction r with
  | nil => simp [sumFiltered]
  | cons a r ih =>
      cases hP : P a with
      | false =>
          simpa [sumFiltered, hP] using
            ih (fun i hi hPi => h i (List.mem_cons_of_mem a hi) hPi)
      | true =>
          have ha := h a List.mem_cons_self hP
          have hr := ih (fun i hi hPi => h i (List.mem_cons_of_mem a hi) hPi)
          simp only [sumFiltered, List.filter_cons, hP, Bool.true_eq,
            ite_true, List.map_cons, List.sum_cons]
          exact Nat.add_le_add ha hr

/-- Pointwise equality is preserved by filtered sequence summation. -/
theorem eq_sum_seq {I : Type _} [DecidableEq I]
    (r : List I) (P : I → Bool) (E1 E2 : I → Nat)
    (h : ∀ i, i ∈ r → P i = true → decide (E1 i = E2 i) = true) :
    sumFiltered r P E1 = sumFiltered r P E2 := by
  induction r with
  | nil => simp [sumFiltered]
  | cons a r ih =>
      cases hP : P a with
      | false =>
          simpa [sumFiltered, hP] using
            ih (fun i hi hPi => h i (List.mem_cons_of_mem a hi) hPi)
      | true =>
          have ha : E1 a = E2 a := of_decide_eq_true (h a List.mem_cons_self hP)
          have hr := ih (fun i hi hPi => h i (List.mem_cons_of_mem a hi) hPi)
          unfold sumFiltered at hr
          simp only [sumFiltered, List.filter_cons, hP, Bool.true_eq,
            ite_true, List.map_cons, List.sum_cons]
          rw [ha, hr]

/-- Predicate implication is preserved by filtered summation. -/
theorem leq_sum_seq_pred {I : Type _} [DecidableEq I]
    (r : List I) (E : I → Nat) (P1 P2 : I → Bool)
    (h : ∀ i, i ∈ r → P1 i = true → P2 i = true) :
    sumFiltered r P1 E ≤ sumFiltered r P2 E := by
  induction r with
  | nil => simp [sumFiltered]
  | cons a r ih =>
      have hr := ih (fun i hi hPi => h i (List.mem_cons_of_mem a hi) hPi)
      cases hP1 : P1 a with
      | false =>
          cases hP2 : P2 a with
          | false => simpa [sumFiltered, hP1, hP2] using hr
          | true =>
              have hadd := le_trans hr
                (Nat.le_add_left (sumFiltered r P2 E) (E a))
              simpa [sumFiltered, hP1, hP2] using hadd
      | true =>
          cases hP2 : P2 a with
          | false =>
              have : P2 a = true := h a List.mem_cons_self hP1
              simp [hP2] at this
          | true =>
              simpa [sumFiltered, hP1, hP2] using
                Nat.add_le_add_left hr (E a)

/-- Alternate binder order for the subsequence-sum monotonicity fact. -/
theorem leq_sum_subseq {I : Type _} [DecidableEq I]
    (r r' : List I) (P : I → Bool) (F : I → Nat)
    (hsub : subseqb r r' = true) :
    sumFiltered r P F ≤ sumFiltered r' P F :=
  sum_le_subseq P F r r' hsub

/-- A duplicate-free included sequence has no greater unfiltered sum. -/
theorem leq_sum_sub_uniq {I : Type _} [DecidableEq I]
    (r : List I) (F : I → Nat) (rs : List I)
    (huniq : r.Nodup) (hsub : ∀ x, x ∈ r → x ∈ rs) :
    sumSeq r F ≤ sumSeq rs F := by
  induction r generalizing rs with
  | nil => simp [sumSeq]
  | cons x r ih =>
      rw [List.nodup_cons] at huniq
      obtain ⟨hxnot, huniq⟩ := huniq
      have hxin : x ∈ rs := hsub x (by simp)
      obtain ⟨left, right, rfl⟩ := List.append_of_mem hxin
      have hsub' : ∀ y, y ∈ r → y ∈ left ++ right := by
        intro y hy
        have hy' := hsub y (List.mem_cons_of_mem x hy)
        simp only [List.mem_append, List.mem_cons] at hy' ⊢
        rcases hy' with hleft | hright
        · exact Or.inl hleft
        · rcases hright with hEq | hright
          · subst y; exact absurd hy hxnot
          · exact Or.inr hright
      have htail := ih (rs := left ++ right) huniq hsub'
      unfold sumSeq at htail
      simp only [sumSeq, List.map_cons, List.sum_cons, List.map_append,
        List.sum_append] at htail ⊢
      omega

/-- A strict pointwise improvement at a retained member makes the sum strict. -/
theorem ltn_sum_leq_seq {I : Type _} [DecidableEq I]
    (r : List I) (P : I → Bool) (E1 E2 : I → Nat) (j : I)
    (hj : j ∈ r) (hPj : P j = true) (hlt : E1 j < E2 j)
    (hle : ∀ i, i ∈ r → P i = true → E1 i ≤ E2 i) :
    sumFiltered r P E1 < sumFiltered r P E2 := by
  induction r with
  | nil => simp at hj
  | cons a r ih =>
      have htail : ∀ i, i ∈ r → P i = true → E1 i ≤ E2 i :=
        fun i hi hPi => hle i (List.mem_cons_of_mem a hi) hPi
      rcases List.mem_cons.mp hj with hja | hj
      · subst a
        have hsumTail := leq_sum_seq r P E1 E2 htail
        simp [sumFiltered, hPj]
        exact Nat.add_lt_add_of_lt_of_le hlt hsumTail
      · have hstrict := ih hj htail
        cases hPa : P a with
        | false => simpa [sumFiltered, hPa] using hstrict
        | true =>
            have ha := hle a List.mem_cons_self hPa
            simp [sumFiltered, hPa]
            exact Nat.add_lt_add_of_le_of_lt ha hstrict

/-- Under pointwise domination, equality of sums is equivalent to equality at every retained item. -/
theorem eq_sum_leq_seq {I : Type _} [DecidableEq I]
    (r : List I) (P : I → Bool) (E1 E2 : I → Nat)
    (hle : ∀ i, i ∈ r → P i = true → E1 i ≤ E2 i) :
    decide (sumFiltered r P E1 = sumFiltered r P E2) =
      r.all (fun x => !P x || decide (E1 x = E2 x)) := by
  induction r with
  | nil => simp [sumFiltered]
  | cons a r ih =>
      have htail : ∀ i, i ∈ r → P i = true → E1 i ≤ E2 i :=
        fun i hi hPi => hle i (List.mem_cons_of_mem a hi) hPi
      cases hPa : P a with
      | false =>
          have iht := ih htail
          unfold sumFiltered at iht ⊢
          simp only [List.filter_cons, hPa, Bool.false_eq, ite_false,
            List.all_cons, Bool.not_false, Bool.true_or]
          exact iht
      | true =>
          have ha := hle a List.mem_cons_self hPa
          have hs := leq_sum_seq r P E1 E2 htail
          have iht := ih htail
          unfold sumFiltered at hs iht ⊢
          simp only [List.filter_cons, hPa, Bool.true_eq,
            ite_true, List.map_cons, List.sum_cons, List.all_cons]
          rw [← iht]
          apply Bool.eq_iff_iff.mpr
          simp only [decide_eq_true_eq, Bool.not_true, Bool.false_or,
            Bool.and_eq_true]
          omega

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

private theorem sumSeq_update_not_mem {Y : Type _} [DecidableEq Y]
    (ys : List Y) (y0 : Y) (c : Nat) (g : Y → Nat)
    (hnot : y0 ∉ ys) :
    sumSeq ys (fun y => if y0 = y then c + g y else g y) = sumSeq ys g := by
  induction ys with
  | nil => simp [sumSeq]
  | cons y ys ih =>
      simp only [List.mem_cons, not_or] at hnot
      have hne : y0 ≠ y := hnot.1
      change (if y0 = y then c + g y else g y) +
          sumSeq ys (fun z => if y0 = z then c + g z else g z) =
        g y + sumSeq ys g
      rw [if_neg hne, ih hnot.2]

private theorem sumSeq_le_update {Y : Type _} [DecidableEq Y]
    (ys : List Y) (y0 : Y) (c : Nat) (g : Y → Nat) :
    sumSeq ys g ≤
      sumSeq ys (fun y => if y0 = y then c + g y else g y) := by
  induction ys with
  | nil => simp [sumSeq]
  | cons y ys ih =>
      unfold sumSeq at ih ⊢
      simp only [List.map_cons, List.sum_cons]
      by_cases hEq : y0 = y
      · rw [if_pos hEq]
        omega
      · rw [if_neg hEq]
        omega

private theorem sumSeq_update_le {Y : Type _} [DecidableEq Y]
    (ys : List Y) (y0 : Y) (c : Nat) (g : Y → Nat)
    (hmem : y0 ∈ ys) :
    c + sumSeq ys g ≤
      sumSeq ys (fun y => if y0 = y then c + g y else g y) := by
  induction ys with
  | nil => simp at hmem
  | cons y ys ih =>
      rcases List.mem_cons.mp hmem with hEq | htailMem
      · subst y
        have hmono := sumSeq_le_update ys y0 c g
        unfold sumSeq at hmono ⊢
        simp only [List.map_cons, List.sum_cons, eq_self, if_true]
        omega
      · by_cases hEq : y0 = y
        · subst y
          have hmono := sumSeq_le_update ys y0 c g
          unfold sumSeq at hmono ⊢
          simp only [List.map_cons, List.sum_cons, eq_self, if_true]
          omega
        · have htail := ih htailMem
          unfold sumSeq at htail ⊢
          simp only [List.map_cons, List.sum_cons, if_neg hEq]
          omega

private theorem sumSeq_update_eq {Y : Type _} [DecidableEq Y]
    (ys : List Y) (y0 : Y) (c : Nat) (g : Y → Nat)
    (hmem : y0 ∈ ys) (hnodup : ys.Nodup) :
    sumSeq ys (fun y => if y0 = y then c + g y else g y) =
      c + sumSeq ys g := by
  induction ys with
  | nil => simp at hmem
  | cons y ys ih =>
      rw [List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hmem with hEq | htailMem
      · subst y
        have htail := sumSeq_update_not_mem ys y0 c g hnodup.1
        unfold sumSeq at htail ⊢
        simp only [List.map_cons, List.sum_cons, eq_self, if_true]
        omega
      · have hne : y0 ≠ y := by
          intro hEq
          subst y
          exact hnodup.1 htailMem
        have htail := ih htailMem hnodup.2
        unfold sumSeq at htail ⊢
        simp only [List.map_cons, List.sum_cons, if_neg hne]
        omega

private theorem sumOverPartitions_nil {X Y : Type _} [DecidableEq Y]
    (xToY : X → Y) (f : X → Nat) (P : X → Bool) (ys : List Y) :
    sumOverPartitions xToY f P [] ys = 0 := by
  have hzero : sumOfPartition xToY f P [] = fun _ => 0 := by
    funext y
    simp [sumOfPartition, sumFiltered]
  unfold sumOverPartitions
  rw [hzero]
  simp [sumSeq]

private theorem sumOverPartitions_cons {X Y : Type _} [DecidableEq Y]
    (xToY : X → Y) (f : X → Nat) (P : X → Bool)
    (x : X) (xs : List X) (ys : List Y) :
    sumOverPartitions xToY f P (x :: xs) ys =
      sumSeq ys (fun y =>
        if P x && decide (xToY x = y) then
          f x + sumOfPartition xToY f P xs y
        else sumOfPartition xToY f P xs y) := by
  induction ys with
  | nil => simp [sumOverPartitions, sumSeq]
  | cons y ys ih =>
      simp only [sumOverPartitions, sumSeq, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]
      cases hkeep : P x && decide (xToY x = y) <;>
        simp [sumOfPartition, sumFiltered, hkeep]

/-- Equal pointwise offsets yield equal sums over equally sized half-open intervals. -/
theorem big_sum_eq_in_eq_sized_intervals
    (t1 t2 d : Nat) (F1 F2 : Nat → Nat)
    (heq : ∀ g, g < d → F1 (t1 + g) = F2 (t2 + g)) :
    (∑ t ∈ Finset.Ico t1 (t1 + d), F1 t) =
      ∑ t ∈ Finset.Ico t2 (t2 + d), F2 t := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Nat.add_succ, Nat.add_succ,
        Finset.sum_Ico_succ_top (Nat.le_add_right t1 d),
        Finset.sum_Ico_succ_top (Nat.le_add_right t2 d)]
      rw [ih (fun g hg => heq g (Nat.lt.step hg)), heq d (Nat.lt_succ_self d)]

/-- Summing all retained items is bounded by summing them partition by partition. -/
theorem sum_over_partitions_le {X Y : Type _} [DecidableEq X] [DecidableEq Y]
    (xToY : X → Y) (f : X → Nat) (P : X → Bool)
    (xs : List X) (ys : List Y)
    (hcovered : ∀ x, x ∈ xs → P x = true → xToY x ∈ ys) :
    sumFiltered xs P f ≤ sumOverPartitions xToY f P xs ys := by
  induction xs with
  | nil => simp [sumFiltered, sumOverPartitions_nil]
  | cons x xs ih =>
      have htail : ∀ z, z ∈ xs → P z = true → xToY z ∈ ys :=
        fun z hz hPz => hcovered z (List.mem_cons_of_mem x hz) hPz
      have hi := ih htail
      cases hPx : P x with
      | false =>
          rw [sumOverPartitions_cons]
          unfold sumOverPartitions at hi
          simpa [sumFiltered, hPx] using hi
      | true =>
          have hmem := hcovered x List.mem_cons_self hPx
          have hup := sumSeq_update_le ys (xToY x) (f x)
            (sumOfPartition xToY f P xs) hmem
          have hleft : f x + sumFiltered xs P f ≤
              f x + sumOverPartitions xToY f P xs ys :=
            Nat.add_le_add_left hi (f x)
          unfold sumOverPartitions at hleft
          rw [show sumFiltered (x :: xs) P f =
              f x + sumFiltered xs P f by simp [sumFiltered, hPx],
            sumOverPartitions_cons]
          exact le_trans hleft (by simpa [hPx] using hup)

/-- Excluding one partition preserves the corresponding partition-sum bound. -/
theorem reorder_summation {X Y : Type _} [DecidableEq X] [DecidableEq Y]
    (xToY : X → Y) (f : X → Nat) (P : X → Bool)
    (xs : List X) (ys : List Y)
    (hcovered : ∀ x, x ∈ xs → P x = true → xToY x ∈ ys)
    (y' : Y) :
    sumFiltered xs (fun x => P x && decide (xToY x ≠ y')) f ≤
      sumOverPartitions xToY f P xs (ys.filter fun y => decide (y ≠ y')) := by
  induction xs with
  | nil => simp [sumFiltered, sumOverPartitions_nil]
  | cons x xs ih =>
      have htail : ∀ z, z ∈ xs → P z = true → xToY z ∈ ys :=
        fun z hz hPz => hcovered z (List.mem_cons_of_mem x hz) hPz
      have hi := ih htail
      cases hPx : P x with
      | false =>
          rw [sumOverPartitions_cons]
          unfold sumOverPartitions at hi
          simpa [sumFiltered, hPx] using hi
      | true =>
          by_cases hxy : xToY x = y'
          · have hnot : xToY x ∉ ys.filter (fun y => decide (y ≠ y')) := by
              simp [hxy]
            have hup := sumSeq_update_not_mem
              (ys.filter fun y => decide (y ≠ y')) (xToY x) (f x)
              (sumOfPartition xToY f P xs) hnot
            rw [sumOverPartitions_cons]
            unfold sumOverPartitions at hi
            have htarget := hi.trans_eq hup.symm
            simpa [sumFiltered, hPx, hxy] using htarget
          · have hmem : xToY x ∈ ys.filter (fun y => decide (y ≠ y')) := by
              simp [hcovered x List.mem_cons_self hPx, hxy]
            have hup := sumSeq_update_le
              (ys.filter fun y => decide (y ≠ y')) (xToY x) (f x)
              (sumOfPartition xToY f P xs) hmem
            have hleft : f x +
                sumFiltered xs (fun z => P z && decide (xToY z ≠ y')) f ≤
                f x + sumOverPartitions xToY f P xs
                  (ys.filter fun y => decide (y ≠ y')) :=
              Nat.add_le_add_left hi (f x)
            unfold sumOverPartitions at hleft
            rw [show sumFiltered (x :: xs)
                (fun z => P z && decide (xToY z ≠ y')) f =
                f x + sumFiltered xs
                  (fun z => P z && decide (xToY z ≠ y')) f by
                  simp [sumFiltered, hPx, hxy],
              sumOverPartitions_cons]
            exact le_trans hleft (by simpa [hPx] using hup)

/-- With unique partition names, partitioning preserves the sum exactly. -/
theorem sum_over_partitions_eq {X Y : Type _} [DecidableEq X] [DecidableEq Y]
    (xToY : X → Y) (f : X → Nat) (P : X → Bool)
    (xs : List X) (ys : List Y)
    (hcovered : ∀ x, x ∈ xs → P x = true → xToY x ∈ ys)
    (hxs : xs.Nodup) (hys : ys.Nodup) :
    sumFiltered xs P f = sumOverPartitions xToY f P xs ys := by
  induction xs with
  | nil => simp [sumFiltered, sumOverPartitions_nil]
  | cons x xs ih =>
      rw [List.nodup_cons] at hxs
      have htail : ∀ z, z ∈ xs → P z = true → xToY z ∈ ys :=
        fun z hz hPz => hcovered z (List.mem_cons_of_mem x hz) hPz
      have hi := ih htail hxs.2
      cases hPx : P x with
      | false =>
          rw [sumOverPartitions_cons]
          unfold sumOverPartitions at hi
          simpa [sumFiltered, hPx] using hi
      | true =>
          have hmem := hcovered x List.mem_cons_self hPx
          have hup := sumSeq_update_eq ys (xToY x) (f x)
            (sumOfPartition xToY f P xs) hmem hys
          unfold sumOverPartitions at hi
          rw [show sumFiltered (x :: xs) P f =
              f x + sumFiltered xs P f by simp [sumFiltered, hPx], hi,
            sumOverPartitions_cons]
          simpa [hPx] using hup.symm

/-- A filtered sum of pointwise monotone functions is monotone. -/
theorem sum_leq_mono {I : Type _} [DecidableEq I]
    (P : I → Bool) (F : I → Nat → Nat) (r : List I)
    (hmono : ∀ i, i ∈ r → Prosa.Util.Rel.monotone (fun x y : Nat => x ≤ y) (F i)) :
    Prosa.Util.Rel.monotone (fun x y : Nat => x ≤ y)
      (fun x => sumFiltered r P (fun i => F i x)) := by
  intro x y hxy
  apply decide_eq_true
  apply leq_sum_seq
  intro i hi _
  exact of_decide_eq_true (hmono i hi x y hxy)

/-- Summing over the unique inhabitant of `Unit` is a no-op. -/
theorem sum_unit1 (F : Unit → Nat) :
    (∑ r : Unit, F r) = F () := by
  simp

/-- Boolean inclusion-exclusion lower bound over a finite Nat interval. -/
theorem pigeonhole_on_interval
    (P1 P2 : Nat → Bool) (t1 t2 n1 n2 : Nat)
    (h1 : n1 ≤ ∑ t ∈ Finset.Ico t1 t2, (P1 t).toNat)
    (h2 : n2 ≤ ∑ t ∈ Finset.Ico t1 t2, (P2 t).toNat) :
    (n1 + n2) - (t2 - t1) ≤
      ∑ t ∈ Finset.Ico t1 t2, (P1 t && P2 t).toNat := by
  have hpoint : ∀ t ∈ Finset.Ico t1 t2,
      (P1 t).toNat + (P2 t).toNat ≤
        1 + (P1 t && P2 t).toNat := by
    intro t _
    cases hP1 : P1 t <;> cases hP2 : P2 t <;> simp [hP1, hP2]
  have hsum := Finset.sum_le_sum hpoint
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Ico] at hsum
  have htotal : n1 + n2 ≤
      (t2 - t1) + ∑ t ∈ Finset.Ico t1 t2, (P1 t && P2 t).toNat :=
    (Nat.add_le_add h1 h2).trans hsum
  apply tsub_le_iff_left.mpr
  simpa [Nat.add_comm] using htotal

private theorem exists_mem_pos_of_sumSeq_pos {X : Type _}
    (xs : List X) (p : X → Nat) (hpos : 0 < sumSeq xs p) :
    ∃ x, x ∈ xs ∧ 0 < p x := by
  induction xs with
  | nil => simp [sumSeq] at hpos
  | cons x xs ih =>
      by_cases hx : 0 < p x
      · exact ⟨x, List.mem_cons_self, hx⟩
      · have htail : 0 < sumSeq xs p := by
          unfold sumSeq at hpos ⊢
          simp only [List.map_cons, List.sum_cons] at hpos
          omega
        obtain ⟨y, hy, hpy⟩ := ih htail
        exact ⟨y, List.mem_cons_of_mem x hy, hpy⟩

/-- A duplicate-free list sum of at least two unit-bounded terms has two distinct ones. -/
theorem sum_ge_2_seq {X : Type _} [DecidableEq X]
    (xs : List X) (p : X → Nat)
    (huniq : xs.Nodup)
    (hle : ∀ x, x ∈ xs → p x ≤ 1)
    (htwo : 2 ≤ sumSeq xs p) :
    ∃ x1 x2,
      decide (x1 ≠ x2) = true ∧ x1 ∈ xs ∧ x2 ∈ xs ∧
      decide (p x1 = 1) = true ∧ decide (p x2 = 1) = true := by
  induction xs with
  | nil => simp [sumSeq] at htwo
  | cons x xs ih =>
      rw [List.nodup_cons] at huniq
      have hpx := hle x List.mem_cons_self
      have htailBound : ∀ y, y ∈ xs → p y ≤ 1 :=
        fun y hy => hle y (List.mem_cons_of_mem x hy)
      have hsplit : p x = 0 ∨ p x = 1 := by omega
      rcases hsplit with hzero | hone
      · have htwoTail : 2 ≤ sumSeq xs p := by
          unfold sumSeq at htwo ⊢
          simp only [List.map_cons, List.sum_cons, hzero, zero_add] at htwo
          exact htwo
        obtain ⟨x1, x2, hne, hx1, hx2, hp1, hp2⟩ :=
          ih huniq.2 htailBound htwoTail
        exact ⟨x1, x2, hne, List.mem_cons_of_mem x hx1,
          List.mem_cons_of_mem x hx2, hp1, hp2⟩
      · have htailPos : 0 < sumSeq xs p := by
          unfold sumSeq at htwo ⊢
          simp only [List.map_cons, List.sum_cons, hone] at htwo
          omega
        obtain ⟨y, hy, hpy⟩ := exists_mem_pos_of_sumSeq_pos xs p htailPos
        have hpyOne : p y = 1 := by
          have := htailBound y hy
          omega
        refine ⟨x, y, ?_, List.mem_cons_self,
          List.mem_cons_of_mem x hy, by simp [hone], by simp [hpyOne]⟩
        simp only [decide_eq_true_eq]
        intro hxy
        subst y
        exact huniq.1 hy

/-- The interval version of `sum_ge_2_seq`. -/
theorem sum_ge_2_nat (t1 t2 : Nat) (p : Nat → Nat)
    (hle : ∀ t, p t ≤ 1)
    (htwo : 2 ≤ ∑ t ∈ Finset.Ico t1 t2, p t) :
    ∃ to1 to2,
      t1 ≤ to1 ∧ to1 < to2 ∧ to2 < t2 ∧
      decide (p to1 = 1) = true ∧ decide (p to2 = 1) = true := by
  let xs := (Finset.Ico t1 t2).toList
  have hsum : sumSeq xs p = ∑ t ∈ Finset.Ico t1 t2, p t := by
    simp [xs, sumSeq]
  have htwoList : 2 ≤ sumSeq xs p := by simpa [hsum] using htwo
  obtain ⟨x1, x2, hne, hx1, hx2, hp1, hp2⟩ :=
    sum_ge_2_seq xs p (Finset.nodup_toList _) (fun x _ => hle x) htwoList
  have hr1 : t1 ≤ x1 ∧ x1 < t2 := by
    simpa [xs] using (Finset.mem_Ico.mp (by simpa [xs] using hx1))
  have hr2 : t1 ≤ x2 ∧ x2 < t2 := by
    simpa [xs] using (Finset.mem_Ico.mp (by simpa [xs] using hx2))
  have hne' : x1 ≠ x2 := of_decide_eq_true hne
  rcases lt_or_gt_of_ne hne' with hlt | hgt
  · exact ⟨x1, x2, hr1.1, hlt, hr2.2, hp1, hp2⟩
  · exact ⟨x2, x1, hr2.1, hgt, hr1.2, hp2, hp1⟩

end Prosa.Util.Sum
