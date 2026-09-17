-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/rbf.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Rbf

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound.MaxArrivalsWorkloadBound

namespace RBF

section RBFProperties

variable {Task : Type _} [DecidableEq Task]
variable (task_cost : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)

variable (higher_eq_priority : FP_policy Task)
variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)

variable (tsk : Task)

variable (max_arrivals : Task → Time → Nat)
variable (H_proper_arrival_curve : proper_arrival_curve job_task arr_seq max_arrivals tsk)

private abbrev task_rbf_val (delta : Time) : Time :=
  task_request_bound_function task_cost max_arrivals tsk delta

include H_proper_arrival_curve in
theorem task_rbf_0_zero :
    task_request_bound_function task_cost max_arrivals tsk 0 = 0 := by
  unfold task_request_bound_function
  have ⟨_, hzero, _⟩ := H_proper_arrival_curve
  unfold zero_arrival_curve at hzero
  rw [hzero]
  simp

include H_proper_arrival_curve in
theorem task_rbf_monotone :
    Monotone (task_request_bound_function task_cost max_arrivals tsk) := by
  intro a b hab
  unfold task_request_bound_function
  have ⟨_, _, hmono⟩ := H_proper_arrival_curve
  unfold monotonic_arrival_curve at hmono
  exact Nat.mul_le_mul_left _ (hmono hab)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

include H_arrival_times_are_consistent H_proper_arrival_curve H_j_arrives H_job_of_tsk in
theorem task_rbf_1_ge_task_cost :
    task_request_bound_function task_cost max_arrivals tsk 1 ≥ task_cost tsk := by
  unfold task_request_bound_function
  suffices h : 1 ≤ max_arrivals tsk 1 by
    calc task_cost tsk = task_cost tsk * 1 := (Nat.mul_one _).symm
      _ ≤ task_cost tsk * max_arrivals tsk 1 := Nat.mul_le_mul_left _ h
  obtain ⟨h_bound, _, _⟩ := H_proper_arrival_curve
  -- Don't unfold is_arrival_bound. Instead, use it directly.
  -- is_arrival_bound : ∀ t1 t2, t1 ≤ t2 → num_arrivals_of_tsk ... ≤ max_arrivals tsk (t2 - t1)
  -- But num_arrivals_of_tsk is private. Let me try a completely different approach.
  -- proper_arrival_curve = is_arrival_bound ∧ zero_arrival_curve ∧ monotonic_arrival_curve
  -- Maybe I should use dsimp to force-inline private defs
  have h_bound2 : ∀ (t1 t2 : Time), t1 ≤ t2 →
    ((jobs_arrived_between arr_seq t1 t2).filter (fun j' => decide (job_task j' = tsk))).length ≤
    max_arrivals tsk (t2 - t1) := by
    intro t1 t2 h12
    have := h_bound t1 t2 h12
    -- this has the private defs, but definitionally should equal our expression
    exact this
  have h_ab := h_bound2 (job_arrival j) (job_arrival j + 1) (Nat.le_add_right _ _)
  simp only [Nat.add_sub_cancel_left] at h_ab
  have h_j_in : j ∈ (jobs_arrived_between arr_seq (job_arrival j) (job_arrival j + 1)).filter (fun j' => decide (job_task j' = tsk)) := by
    rw [List.mem_filter]
    constructor
    · apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j
        (job_arrival j) (job_arrival j + 1) H_j_arrives
      exact ⟨Nat.le_refl _, Nat.lt_succ_of_le (Nat.le_refl _)⟩
    · simp [H_job_of_tsk]
  have h_pos := List.length_pos_of_mem h_j_in
  omega

end RBFProperties

end RBF

end Prosa.Classic.Model.Schedule.Uni.Limited.Rbf
