import Prosa.Classic.Model.Arrival.Jitter.TaskArrival

/-!
Validation-only interface for `classic/model/arrival/jitter/task_arrival.v` (classic family): kernel-checked Lean
equations, exported with their proofs and used by the Rocq certificate as propositional equations
(transport) only.
-/

namespace Prosa.Validation.ClassicJitterTaskArrivalInterface

open Prosa.Classic.Model.Time.Time
open List (Sublist)

universe u

theorem le_trans' {α : Type u} (f : α → time) :
    ∀ a b c : α, decide (f a ≤ f b) = true → decide (f b ≤ f c) = true → decide (f a ≤ f c) = true := by
  intro a b c h1 h2
  simp only [decide_eq_true_eq] at *
  exact Nat.le_trans h1 h2

theorem le_total' {α : Type u} (f : α → time) :
    ∀ a b : α, (decide (f a ≤ f b) || decide (f b ≤ f a)) = true := by
  intro a b
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

theorem bigCat_range' {α : Type u} (m n : Nat) (F : Nat → List α) :
    Prosa.Util.Notation.bigCat m n F =
      ((List.range' 0 (n - m)).map (fun i => F (m + i))).flatten := by
  unfold Prosa.Util.Notation.bigCat
  rw [List.range_eq_range']

theorem mergeSort_isChain {α : Type u} (f : α → time) (l : List α) :
    List.IsChain (fun a b => decide (f a ≤ f b) = true)
      (l.mergeSort (fun j j' => decide (f j ≤ f j'))) := by
  have h := List.pairwise_mergeSort (le := fun j j' => decide (f j ≤ f j'))
    (le_trans' f) (le_total' f) l
  exact List.isChain_iff_pairwise.mpr h

/-- A key class `f y = f x` is kept in order by one merge step of sorted lists: the class members
of the left list precede those of the right list (stability of `List.merge`). -/
theorem merge_filter_class {α : Type u} (f : α → time) (x : α) :
    ∀ (xs ys : List α),
      xs.Pairwise (fun a b => decide (f a ≤ f b) = true) →
      (List.merge xs ys (fun j j' => decide (f j ≤ f j'))).filter (fun y => decide (f y = f x)) =
        xs.filter (fun y => decide (f y = f x)) ++ ys.filter (fun y => decide (f y = f x))
  | [], ys, _ => by rw [List.nil_merge]; rfl
  | a :: xs, [], _ => by rw [List.merge_right, List.filter_nil, List.append_nil]
  | a :: xs, b :: ys, hxs => by
    by_cases h : decide (f a ≤ f b) = true
    · rw [List.cons_merge_cons_pos _ _ _ h, List.filter_cons, List.filter_cons (x := a),
        merge_filter_class f x xs (b :: ys) (List.pairwise_cons.mp hxs).2]
      split <;> rfl
    · rw [List.cons_merge_cons_neg _ _ _ h, List.filter_cons (x := b),
        merge_filter_class f x (a :: xs) ys hxs]
      by_cases hb : decide (f b = f x) = true
      · have hlt : f b < f a := by
          simp only [decide_eq_true_eq] at h
          exact Nat.lt_of_not_le h
        have hnil : (a :: xs).filter (fun y => decide (f y = f x)) = [] := by
          rw [List.filter_eq_nil_iff]
          intro c hc
          simp only [decide_eq_true_eq] at hb ⊢
          intro hcx
          have hac : f a ≤ f c := by
            rcases List.mem_cons.mp hc with hca | hcxs
            · rw [hca]
            · have := (List.pairwise_cons.mp hxs).1 c hcxs
              simp only [decide_eq_true_eq] at this
              exact this
          rw [hcx, ← hb] at hac
          exact absurd hac (Nat.not_le_of_lt hlt)
        rw [if_pos hb, hnil, List.nil_append, List.nil_append, List.filter_cons (x := b), if_pos hb]
      · rw [if_neg hb, List.filter_cons (x := b), if_neg hb]
termination_by xs ys => xs.length + ys.length

/-- `List.mergeSort` keeps each key class `f y = f x` in its original order. -/
theorem mergeSort_filter_class {α : Type u} (f : α → time) (x : α) :
    ∀ (l : List α),
      (l.mergeSort (fun j j' => decide (f j ≤ f j'))).filter (fun y => decide (f y = f x)) =
        l.filter (fun y => decide (f y = f x))
  | [] => by rw [List.mergeSort_nil]
  | [a] => by rw [List.mergeSort_singleton]
  | a :: b :: xs => by
    simp only [List.mergeSort]
    have : (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by
      simp [List.MergeSort.Internal.splitInTwo_fst]; omega
    have : (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by
      simp [List.MergeSort.Internal.splitInTwo_snd]; omega
    rw [merge_filter_class f x _ _
          (List.pairwise_mergeSort (le := fun j j' => decide (f j ≤ f j')) (le_trans' f) (le_total' f) _),
        mergeSort_filter_class f x, mergeSort_filter_class f x, ← List.filter_append,
        List.MergeSort.Internal.splitInTwo_fst_append_splitInTwo_snd]
termination_by l => l.length

end Prosa.Validation.ClassicJitterTaskArrivalInterface
