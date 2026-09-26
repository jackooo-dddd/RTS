-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/tdma.v

import Prosa.Model.Schedule.Tdma

namespace Prosa.Analysis.Facts.Tdma

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Schedule.Tdma
open Prosa.Util.Rel
open Prosa.Util.Seqset

universe u

/-! Proof-local sum facts over the source `foldr` sums.  They are private so the
public declaration set is exactly the six source lemmas. -/

private theorem foldr_sum_filter_le {α : Type u} (f : α → Nat) (P : α → Bool) :
    ∀ xs : List α,
      (xs.filter P).foldr (fun x n => f x + n) 0 ≤ xs.foldr (fun x n => f x + n) 0
  | [] => Nat.le_refl _
  | a :: xs => by
      have ih := foldr_sum_filter_le f P xs
      by_cases h : P a = true
      · simp only [List.filter_cons, h, if_true, List.foldr_cons]; omega
      · simp only [List.filter_cons, h, List.foldr_cons]; simp; omega

private theorem foldr_sum_filter_mono {α : Type u} (f : α → Nat) (P Q : α → Bool) :
    ∀ xs : List α, (∀ x, x ∈ xs → P x = true → Q x = true) →
      (xs.filter P).foldr (fun x n => f x + n) 0 ≤
        (xs.filter Q).foldr (fun x n => f x + n) 0
  | [] => fun _ => Nat.le_refl _
  | a :: xs => fun hPQ => by
      have ih := foldr_sum_filter_mono f P Q xs
        (fun x hx hP => hPQ x (List.mem_cons_of_mem a hx) hP)
      by_cases hP : P a = true
      · have hQ := hPQ a List.mem_cons_self hP
        simp only [List.filter_cons, hP, hQ, if_true, List.foldr_cons]; omega
      · by_cases hQ : Q a = true
        · simp only [List.filter_cons, hP, hQ, if_true, List.foldr_cons]; simp; omega
        · simp only [List.filter_cons, hP, hQ]; simp; omega

/-- A task outside the filter but inside the list contributes separately. -/
private theorem foldr_sum_filter_add_le {α : Type u} [DecidableEq α] (f : α → Nat)
    (P Q : α → Bool) (t : α) :
    ∀ xs : List α, t ∈ xs → P t = false → Q t = true →
      (∀ x, x ∈ xs → P x = true → Q x = true) →
      (xs.filter P).foldr (fun x n => f x + n) 0 + f t ≤
        (xs.filter Q).foldr (fun x n => f x + n) 0
  | [] => fun h => absurd h List.not_mem_nil
  | a :: xs => fun hmem hPt hQt hPQ => by
      have hPQ' : ∀ x, x ∈ xs → P x = true → Q x = true :=
        fun x hx hP => hPQ x (List.mem_cons_of_mem a hx) hP
      by_cases hat : a = t
      · subst hat
        have hmono := foldr_sum_filter_mono f P Q xs hPQ'
        simp only [List.filter_cons, hPt, hQt, if_true, List.foldr_cons]; simp; omega
      · have ht : t ∈ xs := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hat
          · exact h
        have ih := foldr_sum_filter_add_le f P Q t xs ht hPt hQt hPQ'
        by_cases hP : P a = true
        · have hQ := hPQ a List.mem_cons_self hP
          simp only [List.filter_cons, hP, hQ, if_true, List.foldr_cons]; omega
        · by_cases hQ : Q a = true
          · simp only [List.filter_cons, hP, hQ, if_true, List.foldr_cons]; simp; omega
          · simp only [List.filter_cons, hP, hQ]; simp; omega

private theorem foldr_sum_mem_le {α : Type u} [DecidableEq α] (f : α → Nat) (t : α) :
    ∀ xs : List α, t ∈ xs → f t ≤ xs.foldr (fun x n => f x + n) 0
  | [] => fun h => absurd h List.not_mem_nil
  | a :: xs => fun hmem => by
      simp only [List.foldr_cons]
      rcases List.mem_cons.mp hmem with h | h
      · subst h; omega
      · have := foldr_sum_mem_le f t xs h; omega

/-- The offset of `task` plus its own slot fits inside the cycle. -/
private theorem offset_add_slot_le {Task : TaskType} [DecidableEq Task]
    (ts : set Task) [TDMAPolicy Task] (task : Task) (h : task ∈ ts) :
    task_slot_offset ts task + task_time_slot task ≤ TDMA_cycle ts := by
  have hle := foldr_sum_filter_add_le (fun x => task_time_slot x)
    (fun p => slot_order p task && decide (p ≠ task)) (fun _ => true) task ts.val (show task ∈ ts.val from h)
    (by simp) rfl (fun _ _ _ => rfl)
  simpa [task_slot_offset, TDMA_cycle, List.filter_true] using hle

theorem TDMA_cycle_ge_each_time_slot {Task : TaskType} [DecidableEq Task]
    (ts : set Task) [TDMAPolicy Task] (task : Task) :
    task ∈ ts → task_time_slot task ≤ TDMA_cycle ts :=
  fun h => foldr_sum_mem_le (fun x => task_time_slot x) task ts.val (show task ∈ ts.val from h)

theorem TDMA_cycle_positive {Task : TaskType} [DecidableEq Task]
    (ts : set Task) [TDMAPolicy Task] (task : Task) :
    task ∈ ts → valid_time_slot ts → 0 < TDMA_cycle ts :=
  fun h hvalid =>
    Nat.lt_of_lt_of_le (hvalid task h) (TDMA_cycle_ge_each_time_slot ts task h)

theorem Offset_lt_cycle {Task : TaskType} [DecidableEq Task]
    (ts : set Task) [TDMAPolicy Task] (task : Task) :
    task ∈ ts → valid_time_slot ts → task_slot_offset ts task < TDMA_cycle ts := by
  intro h hvalid
  have hle := offset_add_slot_le ts task h
  have hpos : 0 < task_time_slot task := hvalid task h
  dsimp only [duration] at *
  omega

theorem Offset_add_slot_leq_cycle {Task : TaskType} [DecidableEq Task]
    (ts : set Task) [TDMAPolicy Task] (task : Task) :
    task ∈ ts → task_slot_offset ts task + task_time_slot task ≤ TDMA_cycle ts :=
  fun h => offset_add_slot_le ts task h

theorem relation_offset {Task : TaskType} [DecidableEq Task]
    (ts : set Task) [TDMAPolicy Task] :
    antisymmetric_slot_order ts → transitive_slot_order (Task := Task) →
      ∀ tsk1 tsk2 : Task, tsk1 ∈ ts → tsk2 ∈ ts →
        slot_order tsk1 tsk2 = true → decide (tsk1 ≠ tsk2) = true →
          task_slot_offset ts tsk1 + task_time_slot tsk1 ≤ task_slot_offset ts tsk2 := by
  intro hanti htrans tsk1 tsk2 h1 h2 horder hne
  have hne' : tsk1 ≠ tsk2 := of_decide_eq_true hne
  unfold task_slot_offset
  refine foldr_sum_filter_add_le (fun x => task_time_slot x)
    (fun p => slot_order p tsk1 && decide (p ≠ tsk1))
    (fun p => slot_order p tsk2 && decide (p ≠ tsk2)) tsk1 ts.val (show tsk1 ∈ ts.val from h1) (by simp)
    (by simp [horder, hne']) ?_
  intro x hx hP
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hP ⊢
  refine ⟨htrans tsk1 x tsk2 hP.1 horder, ?_⟩
  intro hx2
  subst hx2
  exact hne' (hanti tsk1 x h1 hx horder hP.1)

/-- Inside one cycle, time `t` is in `tsk`'s slot only between its offset and
the end of its slot. -/
private theorem in_slot_bounds (c O s t : Nat) (hO : O < c) (hOs : O + s ≤ c)
    (h : (t + c - O % c) % c < s) : O ≤ t % c ∧ t % c < O + s := by
  have hc : 0 < c := by omega
  rw [Nat.mod_eq_of_lt hO] at h
  have hr : t % c < c := Nat.mod_lt t hc
  have hdecomp := Nat.mod_add_div t c
  have key : (t + c - O) % c = (t % c + c - O) % c := by
    have hsplit : t + c - O = (t % c + c - O) + c * (t / c) := by omega
    rw [hsplit, Nat.add_mul_mod_self_left]
  rw [key] at h
  by_cases hle : O ≤ t % c
  · have hshift : t % c + c - O = (t % c - O) + c := by omega
    rw [hshift, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

theorem task_in_time_slot_uniq {Task : TaskType} [DecidableEq Task]
    (ts : set Task) [TDMAPolicy Task] (task : Task) :
    task ∈ ts → valid_time_slot ts → total_slot_order ts →
      antisymmetric_slot_order ts → transitive_slot_order (Task := Task) →
        ∀ (tsk1 tsk2 : Task) (t : instant),
          tsk1 ∈ ts → 0 < task_time_slot tsk1 →
          tsk2 ∈ ts → 0 < task_time_slot tsk2 →
          task_in_time_slot ts tsk1 t = true →
          task_in_time_slot ts tsk2 t = true → tsk1 = tsk2 := by
  intro _ hvalid htotal hanti htrans tsk1 tsk2 t h1 _ h2 _ hs1 hs2
  have hO1 := Offset_lt_cycle ts tsk1 h1 hvalid
  have hO2 := Offset_lt_cycle ts tsk2 h2 hvalid
  have hS1 := Offset_add_slot_leq_cycle ts tsk1 h1
  have hS2 := Offset_add_slot_leq_cycle ts tsk2 h2
  unfold task_in_time_slot at hs1 hs2
  have b1 := in_slot_bounds _ _ _ _ hO1 hS1 (of_decide_eq_true hs1)
  have b2 := in_slot_bounds _ _ _ _ hO2 hS2 (of_decide_eq_true hs2)
  by_cases heq : tsk1 = tsk2
  · exact heq
  · exfalso
    rcases htotal tsk1 tsk2 h1 h2 with ho | ho
    · have := relation_offset ts hanti htrans tsk1 tsk2 h1 h2 ho (decide_eq_true heq)
      dsimp only [duration, instant] at *
      omega
    · have := relation_offset ts hanti htrans tsk2 tsk1 h2 h1 ho
        (decide_eq_true (Ne.symm heq))
      dsimp only [duration, instant] at *
      omega

end Prosa.Analysis.Facts.Tdma
