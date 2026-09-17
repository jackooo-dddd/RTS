-- Translated from: ../rt-proofs/classic/analysis/apa/bertogna_edf_theory.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Apa.Platform
import Prosa.Classic.Model.Schedule.Apa.Interference
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Prosa.Classic.Model.Schedule.Apa.Constrained_deadlines
import Prosa.Classic.Analysis.Apa.Workload_bound
import Prosa.Classic.Analysis.Apa.Interference_bound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Apa.Bertogna_edf_theory

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
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Schedule.Apa.Platform
open Prosa.Classic.Model.Schedule.Apa.Interference
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Schedule.Apa.Constrained_deadlines hiding apa_work_conserving respects_FP_policy_under_weak_APA
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Apa.Workload_bound.WorkloadBound
open Prosa.Classic.Analysis.Apa.Interference_bound.InterferenceBoundGeneric
open Prosa.Util.Div_mod

namespace ResponseTimeAnalysisEDF

section InterferenceBoundDefs

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable {num_cpus : ℕ}
variable (alpha : task_affinity sporadic_task num_cpus)
variable (tsk : sporadic_task)

def edf_specific_interference_bound (tsk_other : sporadic_task) (R_other : Time) : ℕ :=
  let d_tsk := task_deadline tsk
  let e_other := task_cost tsk_other
  let p_other := task_period tsk_other
  let d_other := task_deadline tsk_other
  (div_floor d_tsk p_other) * e_other +
    min e_other (d_tsk % p_other - (d_other - R_other))

variable (alpha' : affinity num_cpus)
variable (R_prev : List (sporadic_task × Time))
variable (delta : Time)

def interference_bound_edf (tsk_R : sporadic_task × Time) : ℕ :=
  min (interference_bound_generic task_cost task_period tsk delta tsk_R)
      (edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_R.1 tsk_R.2)

private instance decDifferent_task_in_local (tsk_other : sporadic_task) :
    Decidable (different_task_in alpha tsk alpha' tsk_other) :=
  if h1 : tsk_other ≠ tsk then
    if h2 : affinity_intersects alpha' (alpha tsk_other) then
      isTrue ⟨h1, h2⟩
    else
      isFalse (fun ⟨_, h⟩ => h2 h)
  else
    isFalse (fun ⟨h, _⟩ => h1 h)

def total_interference_bound_edf : ℕ :=
  (R_prev.filter (fun p => decide (different_task_in alpha tsk alpha' p.1))).map
    (fun tsk_R => interference_bound_edf task_cost task_period task_deadline tsk delta tsk_R) |>.sum

end InterferenceBoundDefs

attribute [local instance] Classical.propDecidable

section ResponseTimeBound

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)

variable (arr_seq : arrival_sequence Job)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable (ts : List sporadic_task)

variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)

variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable {num_cpus : ℕ}
variable (alpha : task_affinity sporadic_task num_cpus)

variable (sched : schedule Job num_cpus)

variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_respects_affinity :
  respects_affinity job_task sched alpha)
variable (H_work_conserving :
  apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
variable (H_edf_policy :
  respects_JLFP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
    sched alpha (EDF job_arrival job_deadline))

def no_deadline_is_missed_by_tsk (tsk : sporadic_task) : Prop :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

def response_time_bounded_by (tsk : sporadic_task) (R : Time) : Prop :=
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R

variable (alpha' : task_affinity sporadic_task num_cpus)

variable (H_affinity_subset :
  ∀ tsk, tsk ∈ ts → is_subaffinity (alpha' tsk) (alpha tsk))
variable (H_at_least_one_cpu :
  ∀ tsk, tsk ∈ ts → (alpha' tsk).card > 0)

variable (rt_bounds : List (sporadic_task × Time))

variable (H_rt_bounds_contains_all_tasks :
  rt_bounds.map Prod.fst = ts)

variable (H_response_time_is_fixed_point :
  ∀ tsk R,
    (tsk, R) ∈ rt_bounds →
    R = task_cost tsk + div_floor
      (total_interference_bound_edf task_cost task_period task_deadline alpha
        tsk (alpha' tsk) rt_bounds R) (alpha' tsk).card)

variable (H_tasks_miss_no_deadlines :
  ∀ tsk R,
    (tsk, R) ∈ rt_bounds → R ≤ task_deadline tsk)

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
    arrives_in arr_seq j_other →
    job_task j_other = tsk_other →
    (tsk_other, R_other) ∈ rt_bounds →
    job_arrival j_other + R_other < job_arrival j + R →
    completed job_cost sched j_other (job_arrival j_other + R_other))

section LemmasAboutInterferingTasks

variable (tsk_other : sporadic_task)
variable (R_other : Time)
variable (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)

include H_rt_bounds_contains_all_tasks H_response_time_of_tsk_other H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_tsk_other_in_ts :
    tsk_other ∈ ts := by
  sorry

include H_response_time_is_fixed_point H_response_time_of_tsk_other H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_R_other_ge_cost :
    R_other ≥ task_cost tsk_other := by
  sorry

include H_valid_job_parameters H_sporadic_tasks H_constrained_deadlines
  H_tasks_miss_no_deadlines H_valid_task_parameters H_all_jobs_from_taskset
  H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_jobs
  H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks
  H_response_time_is_fixed_point H_tsk_R_in_rt_bounds
  H_response_time_of_tsk_other H_respects_affinity in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time H_response_time_of_tsk_other in
theorem bertogna_edf_workload_bounds_interference :
    task_interference job_arrival job_cost job_task sched alpha j
      tsk_other (job_arrival j) (job_arrival j + R) ≤
    W task_cost task_period tsk_other R_other R := by
  sorry

include H_valid_job_parameters H_sporadic_tasks H_constrained_deadlines
  H_tasks_miss_no_deadlines H_all_jobs_from_taskset
  H_j_arrives H_job_of_tsk H_all_previous_jobs_completed_on_time
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_sequential_jobs
  H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks
  H_tsk_R_in_rt_bounds H_response_time_of_tsk_other H_respects_affinity in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time H_response_time_of_tsk_other in
theorem bertogna_edf_specific_bound_holds :
    task_interference job_arrival job_cost job_task sched alpha j
      tsk_other (job_arrival j) (job_arrival j + R) ≤
    edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_other R_other := by
  sorry

end LemmasAboutInterferingTasks

section DerivingContradiction

include H_completed_jobs_dont_execute H_valid_job_parameters
  H_response_time_is_fixed_point H_job_of_tsk H_j_not_completed
  H_j_arrives H_tsk_R_in_rt_bounds in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_too_much_interference :
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) ≥
    R - task_cost tsk + 1 := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_work_conserving H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_constrained_deadlines H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence H_respects_affinity in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
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
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_all_previous_jobs_complete_by_their_period :
    ∀ t j0,
      arrives_in arr_seq j0 →
      t < job_arrival j + R →
      job_arrival j0 + task_period (job_task j0) ≤ t →
      completed job_cost sched j0
        (job_arrival j0 + task_period (job_task j0)) := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_work_conserving H_valid_job_parameters H_j_arrives
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence H_respects_affinity in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_all_cpus_in_affinity_busy :
    let other_tasks_in_alpha :=
      ts.filter (fun tsk_other => decide (different_task_in alpha tsk (alpha tsk) tsk_other))
    let x := fun tsk_k =>
      task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R)
    (other_tasks_in_alpha.map (fun tsk_k => x tsk_k)).sum =
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) * (alpha tsk).card := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_work_conserving H_valid_job_parameters H_j_arrives
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence
  H_respects_affinity H_affinity_subset in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_all_cpus_in_subaffinity_busy :
    let other_tasks_in_alpha' :=
      ts.filter (fun tsk_other => decide (different_task_in alpha tsk (alpha' tsk) tsk_other))
    let x := fun tsk_k =>
      task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R)
    (other_tasks_in_alpha'.map (fun tsk_k => x tsk_k)).sum ≥
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) * (alpha' tsk).card := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_work_conserving H_valid_job_parameters H_j_arrives
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence
  H_respects_affinity H_affinity_subset H_sequential_jobs in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_alpha'_is_full :
    let scheduled_on_alpha_tsk := fun t tsk_k =>
      task_scheduled_on_affinity job_task sched (alpha tsk) tsk_k t
    let other_tasks_in_alpha' :=
      ts.filter (fun tsk_other => decide (different_task_in alpha tsk (alpha' tsk) tsk_other))
    ∀ t,
      job_arrival j ≤ t ∧ t < job_arrival j + R →
      backlogged job_arrival job_cost sched j t →
      (other_tasks_in_alpha'.filter (fun tsk_k =>
        decide (scheduled_on_alpha_tsk t tsk_k))).length ≥ (alpha' tsk).card := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_work_conserving H_valid_job_parameters H_j_arrives
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence
  H_respects_affinity H_affinity_subset H_sequential_jobs in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_interference_in_non_full_processors :
    let other_tasks_in_alpha' :=
      ts.filter (fun tsk_other => decide (different_task_in alpha tsk (alpha' tsk) tsk_other))
    let x := fun tsk_k =>
      task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R)
    ∀ (delta : Time),
      let num_exceeding := (other_tasks_in_alpha'.filter (fun i => decide (x i ≥ delta))).length
      0 < num_exceeding ∧ num_exceeding < (alpha' tsk).card →
      ((other_tasks_in_alpha'.filter (fun i => decide (x i < delta))).map
        (fun i => x i)).sum ≥
      delta * ((alpha' tsk).card - num_exceeding) := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_work_conserving H_valid_job_parameters H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence
  H_respects_affinity H_affinity_subset H_sequential_jobs in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_minimum_exceeds_interference :
    let other_tasks_in_alpha' :=
      ts.filter (fun tsk_other => decide (different_task_in alpha tsk (alpha' tsk) tsk_other))
    let x := fun tsk_k =>
      task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R)
    ∀ (delta : Time),
      (other_tasks_in_alpha'.map (fun tsk_k => x tsk_k)).sum ≥ delta * (alpha' tsk).card →
      (other_tasks_in_alpha'.map (fun tsk_k => min (x tsk_k) delta)).sum ≥
        delta * (alpha' tsk).card := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_work_conserving H_valid_job_parameters H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence
  H_respects_affinity H_affinity_subset H_at_least_one_cpu in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_interference_on_subaffinity :
    let other_tasks_in_alpha :=
      ts.filter (fun tsk_other => decide (different_task_in alpha tsk (alpha tsk) tsk_other))
    let other_tasks_in_alpha' :=
      ts.filter (fun tsk_other => decide (different_task_in alpha tsk (alpha' tsk) tsk_other))
    let x := fun tsk_k =>
      task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R)
    ∀ (delta : Time),
      (other_tasks_in_alpha.map (fun tsk_k => x tsk_k)).sum ≥ delta * (alpha tsk).card →
      (other_tasks_in_alpha'.map (fun tsk_k => x tsk_k)).sum ≥ delta * (alpha' tsk).card := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_work_conserving H_valid_job_parameters H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence
  H_respects_affinity H_affinity_subset H_at_least_one_cpu
  H_response_time_is_fixed_point H_sequential_jobs in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_sum_exceeds_total_interference :
    let other_tasks_in_alpha' :=
      ts.filter (fun tsk_other => decide (different_task_in alpha tsk (alpha' tsk) tsk_other))
    let x := fun tsk_k =>
      task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R)
    ((rt_bounds.filter (fun p =>
      decide (different_task_in alpha tsk (alpha' tsk) p.1))).map
      (fun p => min (x p.1) (R - task_cost tsk + 1))).sum >
    total_interference_bound_edf task_cost task_period task_deadline alpha
      tsk (alpha' tsk) rt_bounds R := by
  sorry

include H_all_jobs_from_taskset H_valid_task_parameters H_job_of_tsk
  H_sporadic_tasks H_tsk_R_in_rt_bounds
  H_all_previous_jobs_completed_on_time H_tasks_miss_no_deadlines
  H_rt_bounds_contains_all_tasks H_constrained_deadlines
  H_work_conserving H_valid_job_parameters H_j_arrives H_j_not_completed
  H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute
  H_edf_policy H_jobs_come_from_arrival_sequence
  H_respects_affinity H_affinity_subset H_at_least_one_cpu
  H_response_time_is_fixed_point H_sequential_jobs in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_exists_task_that_exceeds_bound :
    let x := fun tsk_k =>
      task_interference job_arrival job_cost job_task sched alpha j tsk_k
        (job_arrival j) (job_arrival j + R)
    ∃ tsk_other R_other,
      (tsk_other, R_other) ∈ rt_bounds ∧
      min (x tsk_other) (R - task_cost tsk + 1) >
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
  H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks
  H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds
  H_respects_affinity H_affinity_subset H_at_least_one_cpu in
include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_affinity H_work_conserving H_edf_policy H_affinity_subset H_at_least_one_cpu H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds in
theorem bertogna_cirinei_response_time_bound_edf :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  sorry

end MainProof

end ResponseTimeBound

end ResponseTimeAnalysisEDF

end Prosa.Classic.Analysis.Apa.Bertogna_edf_theory
