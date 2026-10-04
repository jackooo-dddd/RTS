-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/arrival/jitter/arrival_bounds.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 66)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence
import Prosa.Classic.Model.Arrival.Jitter.TaskArrival

/-!
Bounds on the number of actual (jitter-aware) task arrivals (Rocq module `ArrivalBounds`).

Representation notes (as in `classic/model/arrival/jitter/task_arrival.v`):
* The section-local `Let`s (`actual_job_arrival`, `actual_arrivals`, `num_actual_arrivals`, `by_arrival_time`,
  `sorted_jobs`, `nth_job`, `j_first`, `j_last`, `a_first`, `a_last`) are unfolded; `sort by_arrival_time s` is
  `s.mergeSort (fun j j' => decide (job_arrival j ≤ job_arrival j'))` and `nth elem s i` is `s.getD i elem`.
* `div_ceil` is the classic `Prosa.Classic.Util.DivMod.div_ceil`; `x.-1` is `x - 1`.
* Boolean tests in proposition position are `= true`; `a <= x < b` is `(decide (a ≤ x) && decide (x < b)) = true`.
* Binder lists follow the Rocq contract (e.g. `sporadic_arrival_bound_properties_of_nth` takes no hypotheses,
  and `sporadic_arrival_bound_case_3_contradiction` takes the job `elem` as its last explicit argument).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Arrival.Jitter.ArrivalBounds.ArrivalBounds

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Arrival.Jitter.Job.JobWithJitter
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
open Prosa.Classic.Model.Arrival.Jitter.TaskArrival.TaskArrivalWithJitter
open Prosa.Classic.Util.DivMod (div_ceil)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-- LEAN_HELPER: `x ≤ div_ceil x p * p` for a positive `p`. -/
private theorem le_div_ceil_mul (x p : Nat) (hp : 0 < p) : x ≤ div_ceil x p * p := by
  unfold div_ceil
  split
  · next h => rw [Nat.div_mul_cancel h]
  · rw [Nat.add_mul, Nat.one_mul]; exact Nat.le_of_lt (Nat.lt_div_mul_add hp)

/-- LEAN_HELPER: `div_ceil x p` is positive for positive `x` and `p`. -/
private theorem div_ceil_pos (x p : Nat) (hx : 0 < x) (hp : 0 < p) : 1 ≤ div_ceil x p := by
  unfold div_ceil
  split
  · next h => exact (Nat.le_div_iff_mul_le hp).mpr (by simpa using Nat.le_of_dvd hx h)
  · exact Nat.le_add_left 1 _

theorem sporadic_arrival_bound_no_jobs {Task : Type u} [DecidableEq Task] (task_period task_jitter : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (t1 t2 : time)
    (tsk : Task) (H_no_jobs : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 = 0) :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≤ div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) := by
  rw [H_no_jobs]; exact Nat.zero_le _

theorem sporadic_arrival_bound_more_than_one_point {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (t1 t2 : time)
    (tsk : Task) :
    0 < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 → t1 < t2 := by
  intro ONE
  unfold num_actual_arrivals_of_task at ONE
  obtain ⟨j, IN⟩ := List.exists_mem_of_length_pos ONE
  unfold actual_arrivals_of_task_between at IN
  rw [List.mem_filter] at IN
  have := in_actual_arrivals_implies_arrived_between job_arrival job_jitter arr_seq j t1 t2 IN.1
  simp only [actual_arrival_between, Bool.and_eq_true, decide_eq_true_eq] at this
  omega'

theorem sporadic_arrival_bound_one_job {Task : Type u} [DecidableEq Task] (task_period task_jitter : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (t1 t2 : time)
    (tsk : Task) (H_period_gt_zero : 0 < task_period tsk) (H_no_jobs : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 = 1) :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≤ div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) := by
  have MORE := sporadic_arrival_bound_more_than_one_point job_arrival job_jitter job_task arr_seq t1 t2 tsk
    (by rw [H_no_jobs]; exact Nat.one_pos)
  rw [H_no_jobs]
  exact div_ceil_pos _ _ (by omega') H_period_gt_zero

theorem sporadic_arrival_bound_properties_of_nth {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (t1 t2 : time)
    (tsk : Task) (elem : Job) :
    ∀ idx : Nat,
      idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 →
      (decide (t1 ≤ actual_arrival job_arrival job_jitter (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem)) &&
        decide (actual_arrival job_arrival job_jitter (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) < t2)) = true ∧
      job_task (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) = tsk ∧
      arrives_in arr_seq (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) := by
  intro idx LTidx
  exact sorted_arrivals_properties_of_nth job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx LTidx

theorem sporadic_arrival_bound_distance_between_first_and_last {Task : Type u} [DecidableEq Task] (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (t1 t2 : time) (tsk : Task)
    (H_at_least_two_jobs : 2 ≤ num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2) (elem : Job) :
    job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD 0 elem) + (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) * task_period tsk ≤
      job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) elem) :=
  sorted_arrivals_distance_between_first_and_last task_period job_arrival job_jitter job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks tsk t1 t2 elem (by omega)

theorem sporadic_arrival_bound_last_job_too_far {Task : Type u} [DecidableEq Task] (task_period task_jitter : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk)
    (H_at_least_two_jobs : 2 ≤ num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2)
    (H_many_arrivals : div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2) (elem : Job) :
    job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD 0 elem) + t2 + task_jitter tsk - t1 ≤
      job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) elem) := by
  have DIST := sporadic_arrival_bound_distance_between_first_and_last task_period job_arrival job_jitter job_task
    arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk
    H_at_least_two_jobs elem
  have MORE := sporadic_arrival_bound_more_than_one_point job_arrival job_jitter job_task arr_seq t1 t2 tsk
    (by omega)
  have CEIL := le_div_ceil_mul (t2 + task_jitter tsk - t1) (task_period tsk) H_period_gt_zero
  have MUL : div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) * task_period tsk ≤ (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) * task_period tsk :=
    Nat.mul_le_mul_right _ (by omega)
  generalize div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) = c at *
  generalize num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 = n at *
  generalize (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) * task_period tsk = m at *
  omega'

theorem sporadic_arrival_bound_last_arrives_too_late {Task : Type u} [DecidableEq Task] (task_period task_jitter : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_job_jitter_bounded : ∀ j, arrives_in arr_seq j →
      job_jitter_leq_task_jitter task_jitter job_jitter job_task j = true)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk)
    (H_at_least_two_jobs : 2 ≤ num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2)
    (H_many_arrivals : div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2) (elem : Job) :
    t2 ≤ job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) elem) := by
  have NTH0 := sporadic_arrival_bound_properties_of_nth job_arrival job_jitter job_task arr_seq t1 t2 tsk elem 0
    (by omega)
  have TOOFAR := sporadic_arrival_bound_last_job_too_far task_period task_jitter job_arrival job_jitter job_task
    arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk H_period_gt_zero
    H_at_least_two_jobs H_many_arrivals elem
  obtain ⟨BETWEEN, TSK, ARR⟩ := NTH0
  have JIT := H_job_jitter_bounded _ ARR
  simp only [job_jitter_leq_task_jitter, decide_eq_true_eq, TSK] at JIT
  simp only [actual_arrival, Bool.and_eq_true] at BETWEEN
  have B1 := of_decide_eq_true BETWEEN.1
  have B2 := of_decide_eq_true BETWEEN.2
  omega'

theorem sporadic_arrival_bound_case_3_contradiction {Task : Type u} [DecidableEq Task] (task_period task_jitter : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_job_jitter_bounded : ∀ j, arrives_in arr_seq j →
      job_jitter_leq_task_jitter task_jitter job_jitter job_task j = true)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk)
    (H_at_least_two_jobs : 2 ≤ num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2)
    (H_many_arrivals : div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2) (elem : Job) : False := by
  have LATE := sporadic_arrival_bound_last_arrives_too_late task_period task_jitter job_arrival job_jitter job_task
    arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_job_jitter_bounded H_sporadic_tasks t1 t2
    tsk H_period_gt_zero H_at_least_two_jobs H_many_arrivals elem
  have NTH := sporadic_arrival_bound_properties_of_nth job_arrival job_jitter job_task arr_seq t1 t2 tsk elem
    (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) (by omega)
  obtain ⟨BETWEEN, _, _⟩ := NTH
  simp only [actual_arrival, Bool.and_eq_true] at BETWEEN
  have B1 := of_decide_eq_true BETWEEN.1
  have B2 := of_decide_eq_true BETWEEN.2
  omega'

theorem sporadic_task_arrival_bound_at_least_two_jobs {Task : Type u} [DecidableEq Task] (task_period task_jitter : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_job_jitter_bounded : ∀ j, arrives_in arr_seq j →
      job_jitter_leq_task_jitter task_jitter job_jitter job_task j = true)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk)
    (H_at_least_two_jobs : 2 ≤ num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2) :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≤ div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) := by
  apply Nat.le_of_not_lt
  intro MANY
  have hpos : 0 < (actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).length := by
    unfold num_actual_arrivals_of_task at H_at_least_two_jobs; omega
  obtain ⟨elem, _⟩ := List.exists_mem_of_length_pos hpos
  exact sporadic_arrival_bound_case_3_contradiction task_period task_jitter job_arrival job_jitter job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_job_jitter_bounded H_sporadic_tasks t1 t2 tsk
    H_period_gt_zero H_at_least_two_jobs MANY elem

theorem sporadic_task_with_jitter_arrival_bound {Task : Type u} [DecidableEq Task] (task_period task_jitter : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_job_jitter_bounded : ∀ j, arrives_in arr_seq j →
      job_jitter_leq_task_jitter task_jitter job_jitter job_task j = true)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk) :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≤ div_ceil (t2 + task_jitter tsk - t1) (task_period tsk) := by
  rcases h : num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 with _ | _ | n
  · rw [← h]
    exact sporadic_arrival_bound_no_jobs task_period task_jitter job_arrival job_jitter job_task arr_seq t1 t2 tsk h
  · rw [← h]
    exact sporadic_arrival_bound_one_job task_period task_jitter job_arrival job_jitter job_task arr_seq t1 t2 tsk
      H_period_gt_zero h
  · rw [← h]
    exact sporadic_task_arrival_bound_at_least_two_jobs task_period task_jitter job_arrival job_jitter job_task
      arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_job_jitter_bounded H_sporadic_tasks t1 t2
      tsk H_period_gt_zero (by omega)

end Prosa.Classic.Model.Arrival.Jitter.ArrivalBounds.ArrivalBounds
