-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/arrival_curve_prefix.v

import Prosa.Implementation.Refinements.ArrivalCurve

/-! # Properties of valid arrival-curve prefixes

Representation (as in `ArrivalCurve`): `head (0, 0) s` is `s.headD (0, 0)`; `sorted ltn s` is the accepted
`sortedBool` with `decide (· < ·)`; `x \in xs` is `x ∈ xs`; the section's variables and hypotheses are explicit
binders, in the order of the elaborated statements. -/

set_option linter.dupNamespace false

namespace Prosa.Implementation.Refinements.ArrivalCurvePrefix

open Prosa.Behavior.Time
open Prosa.Implementation.Refinements.ArrivalCurve
open Prosa.Implementation.Refinements.Task
open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
open Prosa.Implementation.Definitions.ArrivalBound
open Prosa.Implementation.Definitions.Task
open Prosa.Model.Task.Concept

private theorem sortedBoolFrom_head {α : Type} {R : α → α → Bool}
    (htrans : ∀ a b c, R a b = true → R b c = true → R a c = true) :
    ∀ (a : α) (xs : List α), sortedBoolFrom R a xs = true → ∀ y ∈ xs, R a y = true
  | _, [], _, _, hy => by simp at hy
  | a, x :: xs, h, y, hy => by
    simp only [sortedBoolFrom, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hy with rfl | hy
    · exact h.1
    · exact htrans _ _ _ h.1 (sortedBoolFrom_head htrans x xs h.2 y hy)

private theorem ltn_steps_trans (a b c : Nat × Nat) :
    ltn_steps a b = true → ltn_steps b c = true → ltn_steps a c = true := by
  intro h1 h2
  simp only [ltn_steps, Bool.and_eq_true, decide_eq_true_eq] at h1 h2 ⊢
  obtain ⟨h1a, h1b⟩ := h1
  obtain ⟨h2a, h2b⟩ := h2
  exact ⟨Nat.lt_trans h1a h2a, Nat.lt_trans h1b h2b⟩

private theorem inter_arrival_valid (p : Nat) (hp : 1 ≤ p) :
    valid_arrival_curve_prefix (inter_arrival_to_prefix p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact decide_eq_true (show 0 < p by omega)
  · intro s hs
    simp only [time_steps_of, steps_of, inter_arrival_to_prefix, List.map_cons, List.map_nil,
      List.mem_singleton] at hs
    subst hs; simp [horizon_of, inter_arrival_to_prefix]; omega
  · rfl
  · simp [specified_bursts, time_steps_of, steps_of, inter_arrival_to_prefix]
  · rfl

/-- The arrival-curve prefix of a task of a valid task set is valid. -/
theorem has_valid_arrival_curve_prefix_tsk :
    ∀ ts : List Task, task_set_with_valid_arrivals ts → ∀ tsk : Task, tsk ∈ ts →
      has_valid_arrival_curve_prefix tsk := by
  intro ts hvalid tsk hin
  have hv := hvalid tsk hin
  refine ⟨get_arrival_curve_prefix tsk, rfl, ?_⟩
  simp only [valid_arrivals] at hv
  simp only [get_arrival_curve_prefix]
  cases harr : concrete_task.task_arrival tsk with
  | Periodic p =>
    rw [harr] at hv
    simp only [decide_eq_true_eq] at hv
    exact inter_arrival_valid _ hv
  | Sporadic m =>
    rw [harr] at hv
    simp only [decide_eq_true_eq] at hv
    exact inter_arrival_valid _ hv
  | ArrivalPrefix e =>
    simp only [harr] at hv
    have hP := valid_arrival_curve_prefix_P e
    rw [hv] at hP
    cases hP with
    | isTrue p => exact p

/-- Every time step of the arrival-curve prefix is positive when the first one is. -/
theorem steps_are_positive_if_first_step_is_positive :
    ∀ ts : List Task, task_set_with_valid_arrivals ts → ∀ tsk : Task, 0 < task_cost tsk → tsk ∈ ts →
      0 < ((steps_of (get_arrival_curve_prefix tsk)).headD (0, 0)).1 →
      ∀ st : Nat, st ∈ get_time_steps_of_task tsk → 0 < st := by
  intro ts hvalid tsk _ hin hpos st hst
  obtain ⟨ac, hac, hvalidac⟩ := has_valid_arrival_curve_prefix_tsk ts hvalid tsk hin
  simp only [get_time_steps_of_task, time_steps_of, hac] at hst
  rw [hac] at hpos
  obtain ⟨_, _, _, _, hsort⟩ := hvalidac
  obtain ⟨h, steps⟩ := ac
  simp only [steps_of] at hst hpos
  cases steps with
  | nil => simp at hst
  | cons s0 rest =>
    simp only [List.map_cons, List.mem_cons, List.mem_map] at hst
    simp only [List.headD_cons] at hpos
    rcases hst with rfl | ⟨⟨t, v⟩, hmem, rfl⟩
    · exact hpos
    · simp only [sorted_ltn_steps, sortedBool, steps_of] at hsort
      have h1 := sortedBoolFrom_head ltn_steps_trans s0 rest hsort (t, v) hmem
      simp only [ltn_steps, Bool.and_eq_true, decide_eq_true_eq] at h1
      exact Nat.lt_trans hpos h1.1

/-- Shifted time steps are positive. -/
theorem nonshifted_offsets_are_positive :
    ∀ ts : List Task, task_set_with_valid_arrivals ts → ∀ tsk : Task, 0 < task_cost tsk → tsk ∈ ts →
      0 < ((steps_of (get_arrival_curve_prefix tsk)).headD (0, 0)).1 →
      ∀ (A : Nat) (offs : List Nat), A ∈ repeat_steps_with_offset tsk offs → 0 < A := by
  intro ts hvalid tsk hcost hin hpos A offs hA
  simp only [repeat_steps_with_offset, List.mem_flatten, List.mem_map] at hA
  obtain ⟨l, ⟨o, _, rfl⟩, hl⟩ := hA
  simp only [time_steps_with_offset, List.mem_map] at hl
  obtain ⟨t, ht, rfl⟩ := hl
  have := steps_are_positive_if_first_step_is_positive ts hvalid tsk hcost hin hpos t ht
  omega

private theorem sortedBoolFrom_map_fst (a : Nat × Nat) :
    ∀ xs : List (Nat × Nat), sortedBoolFrom ltn_steps a xs = true →
      sortedBoolFrom (fun x y => decide (x < y)) a.1 (xs.map Prod.fst) = true
  | [], _ => rfl
  | x :: xs, h => by
    simp only [sortedBoolFrom, Bool.and_eq_true, List.map_cons] at h ⊢
    refine ⟨?_, sortedBoolFrom_map_fst x xs h.2⟩
    simp only [ltn_steps, Bool.and_eq_true, decide_eq_true_eq] at h
    exact decide_eq_true h.1.1

/-- The time steps are strictly increasing. -/
theorem time_steps_sorted :
    ∀ ts : List Task, task_set_with_valid_arrivals ts → ∀ tsk : Task, tsk ∈ ts →
      sortedBool (fun x y => decide (x < y)) (get_time_steps_of_task tsk) = true := by
  intro ts hvalid tsk hin
  obtain ⟨ac, hac, hvalidac⟩ := has_valid_arrival_curve_prefix_tsk ts hvalid tsk hin
  obtain ⟨_, _, _, _, hsort⟩ := hvalidac
  simp only [get_time_steps_of_task, time_steps_of, hac]
  obtain ⟨h, steps⟩ := ac
  simp only [sorted_ltn_steps, sortedBool, steps_of] at hsort ⊢
  cases steps with
  | nil => rfl
  | cons s0 rest => exact sortedBoolFrom_map_fst s0 rest hsort

end Prosa.Implementation.Refinements.ArrivalCurvePrefix
