-- Translated from: ../rt-proofs/classic/analysis/global/jitter/bertogna_edf_theory.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Analysis.Global.Jitter.Workload_bound
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
import Prosa.Classic.Model.Schedule.Global.Jitter.Interference_edf
import Prosa.Classic.Util.Div_mod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_theory

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Workload
open Prosa.Classic.Model.Schedule.Global.Response_time
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Jitter.Job
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines
open Prosa.Classic.Model.Schedule.Global.Jitter.Interference_edf
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Global.Jitter.Workload_bound
open Prosa.Classic.Analysis.Global.Jitter.Workload_bound.WorkloadBoundJitter
open Prosa.Util.Div_mod

namespace ResponseTimeAnalysisEDFJitter

section InterferenceBoundEDF

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

variable (tsk : sporadic_task)

noncomputable def edf_specific_interference_bound
    (tsk_other : sporadic_task) (R_other : Time) : ℕ :=
  let d_tsk := task_deadline tsk
  let e_other := task_cost tsk_other
  let p_other := task_period tsk_other
  let d_other := task_deadline tsk_other
  let j_other := task_jitter tsk_other
  div_floor d_tsk p_other * e_other +
    min e_other (d_tsk % p_other - (d_other - R_other - j_other))

noncomputable def interference_bound_generic
    (task_jitter' : sporadic_task → Time)
    (tsk' : sporadic_task) (delta : Time)
    (tsk_R : sporadic_task × Time) : ℕ :=
  min (W_jitter task_cost task_period task_jitter' tsk_R.1 tsk_R.2 delta)
      (delta - task_cost tsk' + 1)

noncomputable def interference_bound_edf
    (R : Time)
    (tsk_R : sporadic_task × Time) : ℕ :=
  min (interference_bound_generic task_cost task_period task_jitter tsk R tsk_R)
      (edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk tsk_R.1 tsk_R.2)

variable (rt_bounds : List (sporadic_task × Time))
variable (delta : Time)

noncomputable def total_interference_bound_edf : ℕ :=
  ((rt_bounds.filter (fun p => different_task tsk p.1)).map
    (fun tsk_R => interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta tsk_R)).sum

end InterferenceBoundEDF

section JitterInterference

open Classical in
noncomputable def total_interference_jitter
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_jitter : Job → Time)
    {num_cpus : ℕ} (sched : schedule Job num_cpus) (j : Job)
    (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    if Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.backlogged
        job_arrival job_cost job_jitter sched j t then 1 else 0

open Classical in
noncomputable def task_interference_jitter
    {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_task : Job → sporadic_task) (job_jitter : Job → Time)
    {num_cpus : ℕ} (sched : schedule Job num_cpus) (j : Job)
    (tsk_other : sporadic_task) (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      if Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.backlogged
          job_arrival job_cost job_jitter sched j t ∧
         Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleOfSporadicTaskWithJitter.task_scheduled_on
          job_task sched tsk_other cpu t = true then 1 else 0

end JitterInterference

section ResponseTimeBound

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable (task_jitter : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (job_jitter : Job → Time)

variable {arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence Job}

variable (H_sporadic_tasks :
  Prosa.Classic.Model.Arrival.Basic.Task_arrival.sporadic_task_model task_period job_arrival job_task arr_seq)
variable (H_valid_job_parameters :
  ∀ j,
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost
                                   job_deadline job_task job_jitter j)

variable (ts : List sporadic_task)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)
variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_all_jobs_from_taskset :
  ∀ j,
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j → job_task j ∈ ts)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_sequential_jobs : sequential_jobs sched)
variable (H_execute_after_jitter :
  Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.jobs_execute_after_jitter job_arrival job_jitter sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_at_least_one_cpu : num_cpus > 0)

variable (H_work_conserving :
  Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines.work_conserving
    job_arrival job_cost job_jitter arr_seq sched)
variable (H_edf_policy :
  Prosa.Classic.Model.Schedule.Global.Jitter.Interference_edf.InterferenceEDF.respects_JLFP_policy_edf
    job_arrival job_cost job_jitter arr_seq sched
    (EDF job_arrival job_deadline))

variable (rt_bounds : List (sporadic_task × Time))

variable (H_rt_bounds_contains_all_tasks :
  rt_bounds.map Prod.fst = ts)

variable (H_response_time_is_fixed_point :
  ∀ tsk R,
    (tsk, R) ∈ rt_bounds →
    R = task_cost tsk + div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R) num_cpus)

variable (H_tasks_miss_no_deadlines :
  ∀ tsk R,
    (tsk, R) ∈ rt_bounds →
    task_jitter tsk + R ≤ task_deadline tsk)

section Lemmas

variable (tsk : sporadic_task)
variable (R : Time)
variable (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)

variable (j : Job)
variable (H_j_arrives : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (H_j_not_completed :
  ¬ completed job_cost sched j (job_arrival j + job_jitter j + R))

variable (H_all_previous_jobs_completed_on_time :
  ∀ j_other tsk_other R_other,
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j_other →
    job_task j_other = tsk_other →
    (tsk_other, R_other) ∈ rt_bounds →
    job_arrival j_other + task_jitter tsk_other + R_other < job_arrival j + task_jitter tsk + R →
    completed job_cost sched j_other (job_arrival j_other + task_jitter tsk_other + R_other))

section LemmasAboutInterferingTasks

variable (tsk_other : sporadic_task)
variable (R_other : Time)
variable (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)

include H_rt_bounds_contains_all_tasks H_response_time_of_tsk_other

theorem bertogna_edf_tsk_other_in_ts :
    tsk_other ∈ ts := by
  rw [← H_rt_bounds_contains_all_tasks]
  simp only [List.mem_map]
  exact ⟨(tsk_other, R_other), H_response_time_of_tsk_other, rfl⟩

include H_response_time_is_fixed_point

theorem bertogna_edf_R_other_ge_cost :
    R_other ≥ task_cost tsk_other := by
  have h := H_response_time_is_fixed_point tsk_other R_other H_response_time_of_tsk_other
  rw [h]
  exact Nat.le_add_right _ _

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute
  H_tasks_miss_no_deadlines H_j_arrives H_job_of_tsk
  H_all_previous_jobs_completed_on_time

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time H_response_time_of_tsk_other in
theorem bertogna_edf_workload_bounds_interference :
    task_interference_jitter job_arrival job_cost job_task job_jitter sched j tsk_other
      (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) ≤
    W_jitter task_cost task_period task_jitter tsk_other R_other R := by
  sorry

include H_edf_policy H_work_conserving H_at_least_one_cpu

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time H_response_time_of_tsk_other in
theorem bertogna_edf_specific_bound_holds :
    task_interference_jitter job_arrival job_cost job_task job_jitter sched j tsk_other
      (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) ≤
    edf_specific_interference_bound task_cost task_period task_deadline task_jitter tsk tsk_other R_other := by
  sorry

end LemmasAboutInterferingTasks

section DerivingContradiction

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute
  H_at_least_one_cpu H_work_conserving H_edf_policy
  H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point
  H_tasks_miss_no_deadlines
  H_j_arrives H_job_of_tsk
  H_j_not_completed H_all_previous_jobs_completed_on_time
  H_tsk_R_in_rt_bounds

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_too_much_interference :
    total_interference_jitter job_arrival job_cost job_jitter sched j
      (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) ≥
    R - task_cost tsk + 1 := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_interference_by_different_tasks :
    ∀ t j_other,
      job_arrival j + job_jitter j ≤ t ∧ t < job_arrival j + job_jitter j + R →
      Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.backlogged
        job_arrival job_cost job_jitter sched j t →
      scheduled sched j_other t →
      job_task j_other ≠ tsk := by
  sorry

theorem bertogna_edf_all_previous_jobs_complete_by_their_period :
    ∀ t j0,
      t < job_arrival j + job_jitter j + R →
      Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j0 →
      job_arrival j0 + task_period (job_task j0) ≤ t →
      completed job_cost sched j0 (job_arrival j0 + task_period (job_task j0)) := by
  intro t j0 hLT hARR0 hLE
  -- job_task j0 ∈ ts
  have hINts : job_task j0 ∈ ts := H_all_jobs_from_taskset j0 hARR0
  -- Find (job_task j0, R0) ∈ rt_bounds
  have hINmap : job_task j0 ∈ rt_bounds.map Prod.fst := by
    rw [H_rt_bounds_contains_all_tasks]; exact hINts
  simp only [List.mem_map] at hINmap
  obtain ⟨⟨tsk0, R0⟩, hINbounds, hEQ⟩ := hINmap
  simp at hEQ; subst hEQ
  -- Use completion_monotonic to reduce to showing completed at arrival + jitter + R0
  have hNOMISS := H_tasks_miss_no_deadlines (job_task j0) R0 hINbounds
  have hCONSTR := H_constrained_deadlines (job_task j0) hINts
  have hVALID := H_valid_job_parameters j H_j_arrives
  unfold valid_sporadic_job_with_jitter at hVALID
  obtain ⟨_, hJitterBound⟩ := hVALID
  unfold job_jitter_leq_task_jitter at hJitterBound
  rw [H_job_of_tsk] at hJitterBound
  have hJR_le_period : task_jitter (job_task j0) + R0 ≤ task_period (job_task j0) :=
    le_trans hNOMISS hCONSTR
  -- Derive the bound on absolute time
  have hAbsLE : job_arrival j0 + task_jitter (job_task j0) + R0 ≤
      job_arrival j0 + task_period (job_task j0) := by
    -- (a + b) + c ≤ a + d  where b + c ≤ d
    rw [Nat.add_assoc]; exact Nat.add_le_add_left hJR_le_period _
  have hAbsLT : job_arrival j0 + task_jitter (job_task j0) + R0 < job_arrival j + task_jitter tsk + R := by
    calc job_arrival j0 + task_jitter (job_task j0) + R0
        ≤ job_arrival j0 + task_period (job_task j0) := hAbsLE
      _ ≤ t := hLE
      _ < job_arrival j + job_jitter j + R := hLT
      _ ≤ job_arrival j + task_jitter tsk + R := by
          rw [Nat.add_assoc, Nat.add_assoc]; exact Nat.add_le_add_left (Nat.add_le_add_right hJitterBound _) _
  -- Show completed at arrival + jitter + R0
  have hCOMP := H_all_previous_jobs_completed_on_time j0 (job_task j0) R0 hARR0 rfl hINbounds hAbsLT
  -- Now use completion_monotonic
  exact completion_monotonic job_cost sched j0 H_completed_jobs_dont_execute
    (job_arrival j0 + task_jitter (job_task j0) + R0) (job_arrival j0 + task_period (job_task j0))
    hAbsLE hCOMP

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_all_cpus_are_busy :
    ∀ t,
      job_arrival j + job_jitter j ≤ t ∧ t < job_arrival j + job_jitter j + R →
      Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter.backlogged
        job_arrival job_cost job_jitter sched j t →
      ts.countP (fun tsk_other =>
        Prosa.Classic.Model.Schedule.Global.Jitter.Constrained_deadlines.task_is_scheduled
          job_task sched tsk_other t &&
        different_task tsk tsk_other) = num_cpus := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_interference_on_all_cpus :
    ((ts.filter (fun tsk_other => different_task tsk tsk_other)).map
      (fun tsk_k => task_interference_jitter job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R))).sum =
    total_interference_jitter job_arrival job_cost job_jitter sched j
      (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R) * num_cpus := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_interference_in_non_full_processors :
    ∀ (delta : ℕ),
      let other_tasks := ts.filter (fun tsk_other => different_task tsk tsk_other)
      let x := fun tsk_k => task_interference_jitter job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)
      let num_tasks_exceeding := other_tasks.countP (fun i => decide (x i ≥ delta))
      0 < num_tasks_exceeding ∧ num_tasks_exceeding < num_cpus →
      ((other_tasks.filter (fun i => decide (x i < delta))).map x).sum ≥
        delta * (num_cpus - num_tasks_exceeding) := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_minimum_exceeds_interference :
    ∀ (delta : ℕ),
      let other_tasks := ts.filter (fun tsk_other => different_task tsk tsk_other)
      let x := fun tsk_k => task_interference_jitter job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)
      (other_tasks.map x).sum ≥ delta * num_cpus →
      (other_tasks.map (fun tsk_k => min (x tsk_k) delta)).sum ≥ delta * num_cpus := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_sum_exceeds_total_interference :
    let x := fun tsk_k => task_interference_jitter job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)
    ((rt_bounds.filter (fun p => different_task tsk p.1)).map
      (fun ⟨tsk_other, _R_other⟩ =>
        min (x tsk_other) (R - task_cost tsk + 1))).sum >
    total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R := by
  sorry

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time in
theorem bertogna_edf_exists_task_that_exceeds_bound :
    let x := fun tsk_k => task_interference_jitter job_arrival job_cost job_task job_jitter sched j tsk_k
        (job_arrival j + job_jitter j) (job_arrival j + job_jitter j + R)
    ∃ tsk_other R_other,
      (tsk_other, R_other) ∈ rt_bounds ∧
      min (x tsk_other) (R - task_cost tsk + 1) >
        interference_bound_edf task_cost task_period task_deadline task_jitter tsk R (tsk_other, R_other) := by
  sorry

end DerivingContradiction

end Lemmas

section MainProof

variable (tsk : sporadic_task)
variable (R : Time)
variable (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute
  H_at_least_one_cpu H_work_conserving H_edf_policy
  H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point
  H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs H_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines H_tsk_R_in_rt_bounds in
theorem bertogna_cirinei_response_time_bound_edf :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
  sorry

end MainProof

end ResponseTimeBound

end ResponseTimeAnalysisEDFJitter

end Prosa.Classic.Analysis.Global.Jitter.Bertogna_edf_theory
