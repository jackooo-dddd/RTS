-- Translated from: ../rt-proofs/classic/model/arrival/jitter/arrival_bounds.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Arrival.Jitter.Task_arrival
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Util.Div_mod

namespace Prosa.Classic.Model.Arrival.Jitter.Arrival_bounds

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Arrival.Jitter.Job
open Prosa.Classic.Model.Arrival.Jitter.Task_arrival
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Util.Div_mod
open Prosa.Classic.Util.Div_mod

noncomputable def sorted_jobs {Task : Type _} [DecidableEq Task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_jitter : Job → Time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : Time) : List Job :=
  (actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
    (fun j j' => job_arrival j ≤ job_arrival j')

noncomputable def nth_job {Task : Type _} [DecidableEq Task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_jitter : Job → Time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : Time)
    (elem : Job) (idx : ℕ) : Job :=
  (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).getD idx elem

section BoundingActualArrivals

variable {Task : Type _} [DecidableEq Task]
variable (task_period : Task → Time)
variable (task_jitter : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_jitter : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)

variable (H_job_jitter_bounded :
  ∀ j, arrives_in arr_seq j →
    job_jitter j ≤ task_jitter (job_task j))

section UpperBoundOn

variable (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)

variable (t1 t2 : Time)

variable (tsk : Task)
variable (H_period_gt_zero : task_period tsk > 0)

section NoJobs

variable (H_no_jobs : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 = 0)

include H_no_jobs in
theorem sporadic_arrival_bound_no_jobs :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≤
    div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) := by
  rw [H_no_jobs]; exact Nat.zero_le _

end NoJobs

section OneJob

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set in
theorem sporadic_arrival_bound_more_than_one_point
    (h : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 > 0) :
    t1 < t2 := by
  simp only [num_actual_arrivals_of_task, actual_arrivals_of_task_between] at h
  have h_nonempty := List.length_pos_iff_ne_nil.mp h
  have h_exists := List.exists_mem_of_ne_nil _ h_nonempty
  obtain ⟨j, hj⟩ := h_exists
  rw [List.mem_filter] at hj
  obtain ⟨hj_mem, hj_task⟩ := hj
  have hj_between := in_actual_arrivals_implies_arrived_between job_arrival job_jitter arr_seq H_arrival_times_are_consistent j t1 t2 hj_mem
  exact Nat.lt_of_le_of_lt hj_between.1 hj_between.2

variable (H_one_job : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 = 1)

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_one_job H_period_gt_zero H_job_jitter_bounded H_sporadic_tasks in
theorem sporadic_arrival_bound_one_job :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≤
    div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) := by
  rw [H_one_job]
  have hlt : t1 < t2 := by
    apply sporadic_arrival_bound_more_than_one_point job_arrival job_jitter job_task arr_seq
      H_arrival_times_are_consistent H_arrival_sequence_is_a_set t1 t2 tsk
    rw [H_one_job]; omega
  have hpos : t2 + task_jitter tsk - t1 > 0 :=
    Nat.sub_pos_of_lt (Nat.lt_of_lt_of_le hlt (Nat.le_add_right t2 _))
  exact ceil_neq0 (t2 + task_jitter tsk - t1) (task_period tsk) hpos H_period_gt_zero

end OneJob

section AtLeastTwoJobs

variable (H_at_least_two_jobs : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≥ 2)

section DerivingContradiction

variable (H_many_arrivals :
  div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) <
  num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2)

variable (elem : Job)

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks in
theorem sporadic_arrival_bound_properties_of_nth
    (idx : ℕ)
    (h : idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2) :
    t1 ≤ actual_arrival job_arrival job_jitter
      (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) ∧
    actual_arrival job_arrival job_jitter
      (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) < t2 ∧
    job_task
      (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) = tsk ∧
    arrives_in arr_seq
      (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) := by
  exact sorted_arrivals_properties_of_nth job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx h H_arrival_times_are_consistent

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs in
theorem sporadic_arrival_bound_distance_between_first_and_last :
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem
      (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1)) ≥
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0) +
    (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) *
    task_period tsk := by
  have h_ge1 : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≥ 1 := by omega
  exact sorted_arrivals_distance_between_first_and_last task_period job_arrival job_jitter job_task arr_seq tsk t1 t2 elem h_ge1 H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs H_many_arrivals H_period_gt_zero H_job_jitter_bounded in
include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_job_jitter_bounded H_sporadic_tasks H_period_gt_zero H_at_least_two_jobs H_many_arrivals in
theorem sporadic_arrival_bound_last_job_too_far :
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0) +
    t2 + task_jitter tsk - t1 ≤
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem
      (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1)) := by
  set n := num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 with hn_def
  set p := task_period tsk with hp_def
  have DIST := @sporadic_arrival_bound_distance_between_first_and_last Task _ task_period Job _
    job_arrival job_jitter job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    H_sporadic_tasks t1 t2 tsk H_at_least_two_jobs elem
  have h_n_ge2 : n ≥ 2 := H_at_least_two_jobs
  have h_period_pos : p > 0 := H_period_gt_zero
  have h_ceil_lt : div_ceil (t2 + task_jitter tsk - t1) p < n := H_many_arrivals
  have h_ceil_le : div_ceil (t2 + task_jitter tsk - t1) p ≤ n - 1 := Nat.le_sub_one_of_lt h_ceil_lt
  have h_le_period : t2 + task_jitter tsk - t1 ≤ (n - 1) * p := by
    unfold div_ceil at h_ceil_le
    split at h_ceil_le
    · next h_dvd =>
      obtain ⟨k, hk⟩ := h_dvd
      rw [hk, Nat.mul_div_cancel_left _ h_period_pos] at h_ceil_le
      calc t2 + task_jitter tsk - t1 = p * k := hk
        _ ≤ p * (n - 1) := Nat.mul_le_mul_left _ h_ceil_le
        _ = (n - 1) * p := Nat.mul_comm _ _
    · next _ =>
      have hdiv_le : (t2 + task_jitter tsk - t1) / p + 1 ≤ n - 1 := h_ceil_le
      have hlt_mul := Nat.lt_mul_div_succ (t2 + task_jitter tsk - t1) h_period_pos
      exact Nat.le_of_lt (calc t2 + task_jitter tsk - t1 < p * ((t2 + task_jitter tsk - t1) / p + 1) := hlt_mul
        _ ≤ p * (n - 1) := Nat.mul_le_mul_left _ hdiv_le
        _ = (n - 1) * p := Nat.mul_comm _ _)
  have h0lt : 0 < n := by omega
  have h_t1_lt_t2 : t1 < t2 := by
    have h_gt0 : n > 0 := by omega
    exact sporadic_arrival_bound_more_than_one_point job_arrival job_jitter job_task arr_seq
      H_arrival_times_are_consistent H_arrival_sequence_is_a_set t1 t2 tsk h_gt0
  have NTH0 := sporadic_arrival_bound_properties_of_nth task_period job_arrival job_jitter
    job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    t1 t2 tsk elem 0 h0lt
  have h_jitter_bound : job_jitter (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0) ≤ task_jitter tsk := by
    have hj := H_job_jitter_bounded _ NTH0.2.2.2
    rw [NTH0.2.2.1] at hj; exact hj
  have h_t1_le_aa : t1 ≤ actual_arrival job_arrival job_jitter (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0) := NTH0.1
  unfold actual_arrival at h_t1_le_aa
  have h_t1_le : t1 ≤ job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0) + task_jitter tsk := Nat.le_trans h_t1_le_aa (Nat.add_le_add_left h_jitter_bound _)
  set af := job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0)
  have h_assoc : af + t2 + task_jitter tsk - t1 = af + (t2 + task_jitter tsk - t1) := by
    have h1 : t1 ≤ t2 + task_jitter tsk := Nat.le_trans h_t1_lt_t2.le (Nat.le_add_right t2 _)
    rw [show af + t2 + task_jitter tsk = af + (t2 + task_jitter tsk) from by ring]
    rw [Nat.add_sub_assoc h1 af]
  rw [h_assoc]
  exact Nat.le_trans (Nat.add_le_add_left h_le_period _) DIST

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs H_many_arrivals H_period_gt_zero H_job_jitter_bounded in
include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_job_jitter_bounded H_sporadic_tasks H_period_gt_zero H_at_least_two_jobs H_many_arrivals in
theorem sporadic_arrival_bound_last_arrives_too_late :
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem
      (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1)) ≥ t2 := by
  set n := num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2
  set a_last := job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem (n - 1))
  set a_first := job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0)
  set j_first := nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0
  have TOOFAR := @sporadic_arrival_bound_last_job_too_far Task _ task_period task_jitter Job _
    job_arrival job_jitter job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    H_job_jitter_bounded H_sporadic_tasks t1 t2 tsk H_period_gt_zero H_at_least_two_jobs
    H_many_arrivals elem
  have h0lt : 0 < n := by omega
  have NTH0 := sporadic_arrival_bound_properties_of_nth task_period job_arrival job_jitter
    job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    t1 t2 tsk elem 0 h0lt
  -- NTH0.1: t1 ≤ actual_arrival job_arrival job_jitter j_first
  -- actual_arrival = job_arrival + job_jitter, so t1 ≤ a_first + job_jitter j_first
  have h_t1_le_aa : t1 ≤ actual_arrival job_arrival job_jitter j_first := NTH0.1
  unfold actual_arrival at h_t1_le_aa
  -- h_t1_le_aa : t1 ≤ a_first + job_jitter j_first
  have h_jitter_bound : job_jitter j_first ≤ task_jitter (job_task j_first) :=
    H_job_jitter_bounded _ NTH0.2.2.2
  rw [NTH0.2.2.1] at h_jitter_bound
  -- h_jitter_bound : job_jitter j_first ≤ task_jitter tsk
  -- So t1 ≤ a_first + task_jitter tsk
  have h_t1_le : t1 ≤ a_first + task_jitter tsk :=
    Nat.le_trans h_t1_le_aa (Nat.add_le_add_left h_jitter_bound _)
  -- We need: t2 ≤ a_last
  -- We know: a_first + t2 + task_jitter tsk - t1 ≤ a_last  (TOOFAR)
  -- And: t1 ≤ a_first + task_jitter tsk
  -- So: t2 ≤ t2 + (a_first + task_jitter tsk - t1)
  --       = a_first + task_jitter tsk + t2 - t1
  --       = a_first + t2 + task_jitter tsk - t1
  --       ≤ a_last
  -- key idea: t2 ≤ a_first + t2 + task_jitter tsk - t1 ≤ a_last
  -- since t1 ≤ a_first + task_jitter tsk
  suffices h : t2 ≤ a_first + t2 + task_jitter tsk - t1 from Nat.le_trans h TOOFAR
  apply Nat.le_sub_of_add_le
  calc t2 + t1 ≤ t2 + (a_first + task_jitter tsk) := Nat.add_le_add_left h_t1_le t2
    _ = a_first + t2 + task_jitter tsk := by ring

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs H_many_arrivals H_period_gt_zero H_job_jitter_bounded elem in
theorem sporadic_arrival_bound_case_3_contradiction : False := by
  have LATE := @sporadic_arrival_bound_last_arrives_too_late Task _ task_period task_jitter Job _
    job_arrival job_jitter job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    H_job_jitter_bounded H_sporadic_tasks t1 t2 tsk H_period_gt_zero H_at_least_two_jobs
    H_many_arrivals elem
  have hnm1lt : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1 <
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 := by
    have := H_at_least_two_jobs; omega
  have NTH := sporadic_arrival_bound_properties_of_nth task_period job_arrival job_jitter
    job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    t1 t2 tsk elem
    (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) hnm1lt
  have hlt := NTH.2.1  -- actual_arrival ... < t2
  -- LATE: job_arrival(last) ≥ t2
  -- actual_arrival(last) = job_arrival(last) + job_jitter(last) ≥ job_arrival(last) ≥ t2
  -- But hlt: actual_arrival(last) < t2
  -- Contradiction
  unfold actual_arrival at hlt
  -- hlt: job_arrival(last) + job_jitter(last) < t2
  -- LATE: job_arrival(last) ≥ t2
  -- So job_arrival(last) + job_jitter(last) ≥ t2, contradicting hlt
  exact absurd (Nat.le_trans LATE (Nat.le_add_right _ _)) (not_le.mpr hlt)

end DerivingContradiction

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs H_period_gt_zero H_job_jitter_bounded in
theorem sporadic_task_arrival_bound_at_least_two_jobs :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≤
    div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) := by
  by_contra h_not_le
  push_neg at h_not_le
  -- We need an elem : Job. Since n >= 2, the list is nonempty.
  set l := actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2
  have h_nonempty : l.length ≥ 2 := H_at_least_two_jobs
  have h_ne : l ≠ [] := by intro h_eq; simp [h_eq] at h_nonempty
  obtain ⟨elem, _⟩ := List.exists_mem_of_ne_nil l h_ne
  exact sporadic_arrival_bound_case_3_contradiction task_period task_jitter job_arrival job_jitter job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_job_jitter_bounded H_sporadic_tasks t1 t2 tsk H_period_gt_zero H_at_least_two_jobs h_not_le elem

end AtLeastTwoJobs

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_period_gt_zero H_job_jitter_bounded in
include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_job_jitter_bounded H_sporadic_tasks H_period_gt_zero in
theorem sporadic_task_with_jitter_arrival_bound :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≤
    div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) := by
  by_cases h0 : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 = 0
  · rw [h0]; exact Nat.zero_le _
  · by_cases h1 : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 = 1
    · exact sporadic_arrival_bound_one_job task_period task_jitter job_arrival job_jitter
        job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
        H_job_jitter_bounded H_sporadic_tasks t1 t2 tsk H_period_gt_zero h1
    · have h_ge2 : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≥ 2 := by omega
      exact sporadic_task_arrival_bound_at_least_two_jobs task_period task_jitter job_arrival
        job_jitter job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
        H_job_jitter_bounded H_sporadic_tasks t1 t2 tsk H_period_gt_zero h_ge2

end UpperBoundOn

end BoundingActualArrivals

end Prosa.Classic.Model.Arrival.Jitter.Arrival_bounds
