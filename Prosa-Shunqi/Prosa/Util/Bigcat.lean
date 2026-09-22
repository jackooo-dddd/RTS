-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: util/bigcat.v

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Tactic
import Prosa.Util.List
import Prosa.Util.Notation
import Prosa.Util.Tactics

namespace Prosa.Util.Bigcat

open scoped BigOperators
open Prosa.Util.Notation

universe u v

/- These three definitions name source notations. They are Lean helpers rather
than additional source-declaration coverage. Each preserves the enumeration
order and multiplicity of the corresponding MathComp big concatenation. -/

/-- LEAN_HELPER: concatenate a family indexed by all `Fin n` values. -/
def bigCatFin {α : Type u} {n : Nat} (f : Fin n → List α) : List α :=
  (List.ofFn f).flatten

/-- LEAN_HELPER: concatenate a family over the elements satisfying `p`. -/
def bigCatSeq {α : Type u} {β : Type v} (s : List α) (p : α → Bool)
    (f : α → List β) : List β :=
  (s.filter p).flatMap f

/-- LEAN_HELPER: unfiltered sequence-indexed concatenation. -/
def bigCatSeqAll {α : Type u} {β : Type v} (s : List α)
    (f : α → List β) : List β :=
  s.flatMap f

section BigCatNatLemmas

variable {T : Type u} [DecidableEq T]
variable (f : Nat → List T)

theorem mem_bigcat_nat (x : T) (m n j : Nat)
    (hRange : m ≤ j ∧ j < n) (hMem : x ∈ f j) :
    x ∈ bigCat m n f := by
  unfold bigCat
  rw [List.mem_flatten]
  refine ⟨f j, ?_, hMem⟩
  rw [List.mem_map]
  refine ⟨j - m, List.mem_range.mpr ?_, ?_⟩
  · omega
  · congr 1
    omega

theorem mem_bigcat_nat_exists (x : T) (m n : Nat)
    (hMem : x ∈ bigCat m n f) :
    ∃ i, x ∈ f i ∧ m ≤ i ∧ i < n := by
  unfold bigCat at hMem
  rw [List.mem_flatten] at hMem
  obtain ⟨l, hl, hxl⟩ := hMem
  rw [List.mem_map] at hl
  obtain ⟨k, hk, rfl⟩ := hl
  have hklt : k < n - m := List.mem_range.mp hk
  exact ⟨m + k, hxl, by omega, by omega⟩

theorem mem_bigcat_ord (x : T) (n : Nat) (j : Fin n)
    (g : Fin n → List T) (_hj : j.val < n) (hMem : x ∈ g j) :
    x ∈ bigCatFin g := by
  unfold bigCatFin
  rw [List.mem_flatten]
  refine ⟨g j, ?_, hMem⟩
  simpa only [List.mem_ofFn] using (show ∃ i, g i = g j from ⟨j, rfl⟩)

theorem bigcat_nat_uniq
    (hUniqSeq : ∀ i, (f i).Nodup)
    (hNoElementsInCommon : ∀ x i₁ i₂, x ∈ f i₁ → x ∈ f i₂ → i₁ = i₂)
    (n₁ n₂ : Nat) :
    (bigCat n₁ n₂ f).Nodup := by
  unfold bigCat
  generalize hk : n₂ - n₁ = k
  clear hk n₂
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.flatten_append]
      simp only [List.map_singleton, List.flatten_singleton]
      rw [List.nodup_append]
      refine ⟨ih, hUniqSeq (n₁ + k), ?_⟩
      intro a ha b hb hab
      have ha' : a ∈ bigCat n₁ (n₁ + k) f := by
        unfold bigCat
        simpa using ha
      obtain ⟨i, hi, hiLower, hiUpper⟩ :=
        mem_bigcat_nat_exists f a n₁ (n₁ + k) ha'
      have hb' : a ∈ f (n₁ + k) := hab ▸ hb
      have hEq := hNoElementsInCommon a i (n₁ + k) hi hb'
      omega

theorem bigcat_nat_filter_eq_filter_bigcat_nat
    {X : Type u} (F : Nat → List X) (P : X → Bool) (t₁ t₂ : Nat) :
    (bigCat t₁ t₂ F).filter P = bigCat t₁ t₂ (fun t => (F t).filter P) := by
  unfold bigCat
  suffices h : ∀ indices : List Nat,
      ((indices.map fun i => F (t₁ + i)).flatten).filter P =
        (indices.map fun i => (F (t₁ + i)).filter P).flatten by
    exact h (_root_.List.range (t₂ - t₁))
  intro indices
  induction indices with
  | nil => rfl
  | cons i indices ih => simp only [List.map_cons, List.flatten_cons, List.filter_append, ih]

theorem size_big_nat {X : Type u} (F : Nat → List X) (t₁ t₂ : Nat) :
    (∑ t ∈ Finset.Ico t₁ t₂, (F t).length) = (bigCat t₁ t₂ F).length := by
  by_cases h : t₁ ≤ t₂
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    clear h
    induction d with
    | zero => simp [bigCat]
    | succ d ih =>
        rw [Nat.add_succ, Finset.sum_Ico_succ_top (by omega)]
        unfold bigCat
        have hsub : t₁ + d + 1 - t₁ = d + 1 := by omega
        rw [hsub, List.range_succ, List.map_append]
        simp only [List.map_singleton, List.flatten_append, List.flatten_singleton,
          List.length_append]
        simpa [bigCat, Nat.add_sub_cancel_left] using
          congrArg (fun z => z + (F (t₁ + d)).length) ih
  · have hle : t₂ ≤ t₁ := Nat.le_of_not_ge h
    rw [Finset.Ico_eq_empty_of_le hle]
    simp [bigCat, Nat.sub_eq_zero_of_le hle]

end BigCatNatLemmas

section BigCatLemmas

variable {X : Type u} {Y : Type v}
variable [DecidableEq X] [DecidableEq Y]
variable (f : X → List Y)

theorem mem_bigcat (x : X) (y : Y) (s : List X)
    (hXs : x ∈ s) (hY : y ∈ f x) :
    y ∈ bigCatSeqAll s f := by
  simp only [bigCatSeqAll, List.mem_flatMap]
  exact ⟨x, hXs, hY⟩

theorem mem_bigcat_exists (P : X → Bool) (s : List X) (y : Y)
    (hMem : y ∈ bigCatSeq s P f) :
    ∃ x, x ∈ s ∧ y ∈ f x := by
  simp only [bigCatSeq, List.mem_flatMap, List.mem_filter] at hMem
  obtain ⟨x, ⟨hXs, _hPx⟩, hY⟩ := hMem
  exact ⟨x, hXs, hY⟩

theorem bigcat_filter_eq_filter_bigcat (xss : List X) (P : Y → Bool) :
    (bigCatSeqAll xss f).filter P =
      bigCatSeqAll xss (fun x => (f x).filter P) := by
  induction xss with
  | nil => rfl
  | cons x xs ih =>
      simp only [bigCatSeqAll, List.flatMap_cons, List.filter_append]
      simpa [bigCatSeqAll] using congrArg (fun tail => (f x).filter P ++ tail) ih

theorem bigcat_uniq {xs : List X} {P : X → Bool}
    (hUniqF : ∀ x, P x = true → (f x).Nodup)
    (hNoElementsInCommon : ∀ x y z, x ∈ f y → x ∈ f z → y = z)
    (hXs : xs.Nodup) :
    (bigCatSeq xs P f).Nodup := by
  unfold bigCatSeq
  rw [List.nodup_flatMap]
  constructor
  · intro x hx
    exact hUniqF x (List.of_mem_filter hx)
  · apply (hXs.filter P).pairwise_of_forall_ne
    intro y hy z hz hyz
    change List.Disjoint (f y) (f z)
    rw [List.disjoint_left]
    intro item hItemY hItemZ
    exact hyz (hNoElementsInCommon item y z hItemY hItemZ)

section BigCatWithCancelFunctions

variable (g : Y → X)
theorem seq_different_elements_nil
    (hGCancelsF : ∀ x y, y ∈ f x → g y = x)
    (x₁ x₂ : X) (hNe : x₁ ≠ x₂) :
    (f x₁).filter (fun x => decide (g x = x₂)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro y hy
  intro hgyTrue
  have hgy : g y = x₂ := of_decide_eq_true hgyTrue
  apply hNe
  exact (hGCancelsF x₁ y hy).symm.trans hgy

theorem bigcat_seq_uniqK
    (hGCancelsF : ∀ x y, y ∈ f x → g y = x)
    (y : X) (xs : List X)
    (hY : y ∈ xs) (hXs : xs.Nodup) :
    bigCatSeqAll xs (fun x => (f x).filter (fun x' => decide (g x' = y))) = f y := by
  induction xs with
  | nil => simp at hY
  | cons x xs ih =>
      have hCons := List.nodup_cons.mp hXs
      rcases List.mem_cons.mp hY with hxy | hyTail
      · subst x
        have hHead : (f y).filter (fun x' => decide (g x' = y)) = f y := by
          apply List.filter_eq_self.mpr
          intro z hz
          exact decide_eq_true (hGCancelsF y z hz)
        have hTail :
            bigCatSeqAll xs (fun x => (f x).filter (fun x' => decide (g x' = y))) = [] := by
          unfold bigCatSeqAll
          apply List.flatMap_eq_nil_iff.mpr
          intro z hz
          apply seq_different_elements_nil f g hGCancelsF z y
          intro hzy
          apply hCons.1
          simpa [hzy] using hz
        simp only [bigCatSeqAll, List.flatMap_cons]
        rw [hHead]
        unfold bigCatSeqAll at hTail
        rw [hTail, List.append_nil]
      · have hxy : x ≠ y := by
          intro h
          apply hCons.1
          simpa [h] using hyTail
        have hHead := seq_different_elements_nil f g hGCancelsF x y hxy
        simp only [bigCatSeqAll, List.flatMap_cons]
        rw [hHead, List.nil_append]
        have hRec := ih hyTail hCons.2
        unfold bigCatSeqAll at hRec
        exact hRec

end BigCatWithCancelFunctions

end BigCatLemmas

section BigCatPartitionLemma

variable {X : Type u} {Y : Type v}
variable [DecidableEq X] [DecidableEq Y]

theorem bigcat_partitions (xs : List X) (ys : List Y) (P : X → Bool)
    (xToY : X → Y)
    (hNoPartitionMissing : ∀ x, x ∈ xs → P x = true → xToY x ∈ ys)
    (j : X) :
    decide (j ∈ xs.filter P) =
      decide (j ∈ bigCatSeqAll ys
        (fun y => xs.filter (fun x => P x && decide (xToY x = y)))) := by
  apply Bool.decide_congr
  constructor
  · intro hLeft
    obtain ⟨hjXs, hjP⟩ := List.mem_filter.mp hLeft
    apply mem_bigcat (fun y => xs.filter (fun x => P x && decide (xToY x = y)))
      (xToY j) j ys
    · exact hNoPartitionMissing j hjXs hjP
    · apply List.mem_filter.mpr
      exact ⟨hjXs, by simp [hjP]⟩
  · intro hRight
    change j ∈ ys.flatMap (fun y => xs.filter (fun x => P x && decide (xToY x = y))) at hRight
    obtain ⟨y, _hy, hjPart⟩ := List.mem_flatMap.mp hRight
    obtain ⟨hjXs, hjPred⟩ := List.mem_filter.mp hjPart
    have hjBoth : P j = true ∧ decide (xToY j = y) = true := by
      simpa only [Bool.and_eq_true] using hjPred
    have hjP : P j = true := hjBoth.1
    exact List.mem_filter.mpr ⟨hjXs, hjP⟩

end BigCatPartitionLemma

end Prosa.Util.Bigcat
