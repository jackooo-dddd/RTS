-- Translated from: ../rt-proofs/classic/analysis/global/basic/bertogna_edf_theory.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Analysis.Global.Basic.Workload_bound
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.Constrained_deadlines
import Prosa.Classic.Model.Schedule.Global.Basic.Interference_edf
import Prosa.Classic.Analysis.Global.Basic.Interference_bound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Basic.Bertogna_edf_theory

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference
open Prosa.Classic.Model.Schedule.Global.Basic.Constrained_deadlines.ConstrainedDeadlines
open Prosa.Classic.Model.Schedule.Global.Basic.Interference_edf.InterferenceEDF hiding respects_JLFP_policy
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Global.Basic.Workload_bound.WorkloadBound
open Prosa.Classic.Analysis.Global.Basic.Interference_bound.InterferenceBoundGeneric
open Prosa.Util.Div_mod

attribute [local instance] Classical.propDecidable

namespace ResponseTimeAnalysisEDF

section InterferenceBoundDefs

variable {sporadic_task : Type} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (tsk : sporadic_task)
variable (delta : Time)

def edf_specific_interference_bound (tsk_other : sporadic_task) (R_other : Time) : ℕ :=
  let d_tsk := task_deadline tsk
  let e_other := task_cost tsk_other
  let p_other := task_period tsk_other
  let d_other := task_deadline tsk_other
  (div_floor d_tsk p_other) * e_other +
    min e_other (d_tsk % p_other - (d_other - R_other))

def interference_bound_edf (tsk_R : sporadic_task × Time) : ℕ :=
  min (interference_bound_generic task_cost task_period tsk delta tsk_R)
      (edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_R.1 tsk_R.2)

def total_interference_bound_edf (R_prev : List (sporadic_task × Time)) : ℕ :=
  (R_prev.filter (fun p => different_task tsk p.1)).map
    (fun tsk_R => interference_bound_edf task_cost task_period task_deadline tsk delta tsk_R) |>.sum

end InterferenceBoundDefs

section ResponseTimeBound

variable {sporadic_task : Type} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)

variable (arr_seq : arrival_sequence Job)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable (ts : List sporadic_task)

variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_at_least_one_cpu : num_cpus > 0)

variable (H_work_conserving :
  work_conserving job_arrival job_cost arr_seq sched)
variable (H_edf_policy :
  Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform.respects_JLFP_policy
    job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline))

noncomputable def no_deadline_is_missed_by_tsk (tsk : sporadic_task) : Prop :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

def response_time_bounded_by (tsk : sporadic_task) (R : Time) : Prop :=
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

variable (rt_bounds : List (sporadic_task × Time))

variable (H_rt_bounds_contains_all_tasks :
  rt_bounds.map Prod.fst = ts)

variable (H_response_time_is_fixed_point :
  ∀ tsk R,
    (tsk, R) ∈ rt_bounds →    R = task_cost tsk + div_floor
      (total_interference_bound_edf task_cost task_period task_deadline tsk R rt_bounds) num_cpus)

variable (H_tasks_miss_no_deadlines :
  ∀ tsk_other R,
    (tsk_other, R) ∈ rt_bounds → R ≤ task_deadline tsk_other)

section Lemmas

variable (tsk : sporadic_task)
variable (R : Time)
variable (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (H_j_not_completed :
  ¬ completed job_cost sched j (job_arrival j + R))

variable (H_all_previous_jobs_completed_on_time :
  ∀ j_other tsk_other R_other,
    arrives_in arr_seq j_other →    job_task j_other = tsk_other →    (tsk_other, R_other) ∈ rt_bounds →    job_arrival j_other + R_other < job_arrival j + R →    completed job_cost sched j_other (job_arrival j_other + R_other))

section LemmasAboutInterferingTasks

variable (tsk_other : sporadic_task)
variable (R_other : Time)
variable (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)

include H_rt_bounds_contains_all_tasks H_response_time_of_tsk_other in
theorem bertogna_edf_tsk_other_in_ts :
    tsk_other ∈ ts := by
  rw [← H_rt_bounds_contains_all_tasks]
  simp only [List.mem_map]
  exact ⟨(tsk_other, R_other), H_response_time_of_tsk_other, rfl⟩
include H_response_time_is_fixed_point H_response_time_of_tsk_other in
theorem bertogna_edf_R_other_ge_cost :
    task_cost tsk_other ≤ R_other := by
  have h := H_response_time_is_fixed_point tsk_other R_other H_response_time_of_tsk_other
  rw [h]
  exact Nat.le_add_right _ _

include H_valid_job_parameters H_sporadic_tasks H_constrained_deadlines
  H_tasks_miss_no_deadlines H_valid_task_parameters H_all_jobs_from_taskset
  H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu
  H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks
  H_response_time_is_fixed_point H_tsk_R_in_rt_bounds
  H_response_time_of_tsk_other in
theorem bertogna_edf_workload_bounds_interference :
    task_interference job_arrival job_cost job_task sched j tsk_other
      (job_arrival j) (job_arrival j + R) ≤    W task_cost task_period tsk_other R_other R := by
  sorry

include H_valid_job_parameters H_sporadic_tasks H_constrained_deadlines
  H_tasks_miss_no_deadlines H_all_jobs_from_taskset
  H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_jobs H_at_least_one_cpu
  H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks
  H_tsk_R_in_rt_bounds H_response_time_of_tsk_other in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time H_response_time_of_tsk_other in
theorem bertogna_edf_specific_bound_holds :
    task_interference job_arrival job_cost job_task sched j tsk_other
      (job_arrival j) (job_arrival j + R) ≤    edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_other R_other := by
  sorry

end LemmasAboutInterferingTasks

section DerivingContradiction

include H_completed_jobs_dont_execute H_valid_job_parameters
  H_response_time_is_fixed_point H_job_of_tsk H_j_not_completed
  H_j_arrives H_tsk_R_in_rt_bounds in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_too_much_interference :
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) ≤    R - task_cost tsk + 1 := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_work_conserving H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_constrained_deadlines H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_interference_by_different_tasks :
    ∀ t j_other,
      job_arrival j ≤ t ∧ t < job_arrival j + R →
      arrives_in arr_seq j_other →
      backlogged job_arrival job_cost sched j t →
      scheduled sched j_other t →
      job_task j_other ≠ tsk := by
  sorry

include H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_tasks_miss_no_deadlines H_all_jobs_from_taskset
  H_all_previous_jobs_completed_on_time H_completed_jobs_dont_execute
  H_j_arrives in
theorem bertogna_edf_all_previous_jobs_complete_by_their_period :
    ∀ t j0,
      arrives_in arr_seq j0 →      t < job_arrival j + R →      job_arrival j0 + task_period (job_task j0) ≤ t →      completed job_cost sched j0
        (job_arrival j0 + task_period (job_task j0)) := by
  intro t j0 ARR0 LEt LE
  have FROMTS := H_all_jobs_from_taskset j0 ARR0
  have hmap : job_task j0 ∈ rt_bounds.map Prod.fst := by
    rw [H_rt_bounds_contains_all_tasks]; exact FROMTS
  simp only [List.mem_map] at hmap
  obtain ⟨⟨tsk', R0⟩, IN, htsk'⟩ := hmap
  simp at htsk'; subst htsk'
  have hRD : R0 ≤ task_deadline (job_task j0) := H_tasks_miss_no_deadlines _ _ IN
  have hDP : task_deadline (job_task j0) ≤ task_period (job_task j0) :=
    H_constrained_deadlines _ FROMTS
  have hRP : R0 ≤ task_period (job_task j0) := Nat.le_trans hRD hDP
  apply completion_monotonic job_cost sched j0 H_completed_jobs_dont_execute
    (job_arrival j0 + R0) (job_arrival j0 + task_period (job_task j0))
  · exact Nat.add_le_add_left hRP _
  · apply H_all_previous_jobs_completed_on_time j0 (job_task j0) R0 ARR0 rfl IN
    calc job_arrival j0 + R0
        ≤ job_arrival j0 + task_period (job_task j0) := Nat.add_le_add_left hRP _
      _ ≤ t := LE
      _ < job_arrival j + R := LEt

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_work_conserving H_valid_job_parameters H_j_arrives
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_all_cpus_are_busy :
    ∀ t,
      job_arrival j ≤ t ∧ t < job_arrival j + R →
      backlogged job_arrival job_cost sched j t →      (ts.filter (fun tsk_other =>
        decide (task_is_scheduled job_task sched tsk_other t) &&
        different_task tsk tsk_other)).length = num_cpus := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_work_conserving H_jobs_come_from_arrival_sequence
  H_tsk_R_in_rt_bounds H_all_previous_jobs_completed_on_time
  H_tasks_miss_no_deadlines H_rt_bounds_contains_all_tasks
  H_constrained_deadlines H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_valid_job_parameters in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_interference_on_all_cpus :
    ((ts.filter (fun tsk_other => different_task tsk tsk_other)).map
      (fun tsk_k => task_interference job_arrival job_cost job_task sched j tsk_k
        (job_arrival j) (job_arrival j + R))).sum =
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) * num_cpus := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_jobs_come_from_arrival_sequence H_constrained_deadlines
  H_sequential_jobs H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_work_conserving H_valid_job_parameters
  H_rt_bounds_contains_all_tasks in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_interference_in_non_full_processors :
    let other_tasks := ts.filter (fun tsk_other => different_task tsk tsk_other)
    let x_val := fun (tsk_k : sporadic_task) =>
      task_interference job_arrival job_cost job_task sched j tsk_k
        (job_arrival j) (job_arrival j + R)
    ∀ (delta' : Time),
      let num_exceeding := (other_tasks.filter (fun i => decide (x_val i ≤ delta'))).length
      0 < num_exceeding ∧ num_exceeding < num_cpus →      ((other_tasks.filter (fun i => decide (x_val i < delta'))).map
        (fun i => x_val i)).sum ≤      delta' * (num_cpus - num_exceeding) := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_jobs_come_from_arrival_sequence H_constrained_deadlines
  H_sequential_jobs H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_work_conserving H_valid_job_parameters
  H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point
  H_at_least_one_cpu in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_minimum_exceeds_interference :
    let other_tasks := ts.filter (fun tsk_other => different_task tsk tsk_other)
    let x_val := fun (tsk_k : sporadic_task) =>
      task_interference job_arrival job_cost job_task sched j tsk_k
        (job_arrival j) (job_arrival j + R)
    ∀ (delta' : Time),
      (other_tasks.map (fun tsk_k => x_val tsk_k)).sum ≤ delta' * num_cpus →      (other_tasks.map (fun tsk_k => min (x_val tsk_k) delta')).sum ≤        delta' * num_cpus := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_jobs_come_from_arrival_sequence H_constrained_deadlines
  H_sequential_jobs H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_work_conserving H_valid_job_parameters
  H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point
  H_at_least_one_cpu in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_sum_exceeds_total_interference :
    let x_val := fun (tsk_k : sporadic_task) =>
      task_interference job_arrival job_cost job_task sched j tsk_k
        (job_arrival j) (job_arrival j + R)
    ((rt_bounds.filter (fun p => different_task tsk p.1)).map
      (fun p => min (x_val p.1) (R - task_cost tsk + 1))).sum >
    total_interference_bound_edf task_cost task_period task_deadline tsk R rt_bounds := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_jobs_come_from_arrival_sequence H_constrained_deadlines
  H_sequential_jobs H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_work_conserving H_valid_job_parameters
  H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point
  H_at_least_one_cpu in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_exists_task_that_exceeds_bound :
    let x_val := fun (tsk_k : sporadic_task) =>
      task_interference job_arrival job_cost job_task sched j tsk_k
        (job_arrival j) (job_arrival j + R)
    ∃ tsk_other R_other,
      (tsk_other, R_other) ∈ rt_bounds ∧
      min (x_val tsk_other) (R - task_cost tsk + 1) >
        interference_bound_edf task_cost task_period task_deadline tsk R
          (tsk_other, R_other) := by
  sorry

end DerivingContradiction

end Lemmas

section MainProof

variable (tsk : sporadic_task)
variable (R : Time)
variable (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks
  H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds in
theorem bertogna_cirinei_response_time_bound_edf :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  sorry

end MainProof

end ResponseTimeBound

end ResponseTimeAnalysisEDF

end Prosa.Classic.Analysis.Global.Basic.Bertogna_edf_theory
