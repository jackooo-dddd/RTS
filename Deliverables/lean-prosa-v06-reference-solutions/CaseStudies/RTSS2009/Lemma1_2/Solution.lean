import CaseStudies.RTSS2009.Lemma1_2.Statement
import CaseStudies.Support.Common

/-! Reference solution of benchmark task `2009-RTSS-Lemma1_2`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTSS2009.Lemma1_2.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Util.DivMod (div_floor div_ceil)
open Prosa.Util.Sum (sumSeq sumFiltered)

theorem Lemma1_09 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_priority_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_antisymmetric : FP_is_antisymmetric_over_task_set higher_eq_priority ts.val)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (j_has_worstcase_responsetime : ∀ (j0 : Job) (x : Nat), arrives_in arr_seq j0 → job_task j0 = tsk →
      completed job_cost sched j (job_arrival j + x) = true →
      completed job_cost sched j0 (job_arrival j0 + x) = true)
    (t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      hp_busy job_task ts num_cpus sched higher_eq_priority tsk t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ hp_busy job_task ts num_cpus sched higher_eq_priority tsk (t0 sched j - 1))
    (carry_in_job_unique : ∀ (tsk_other : sporadic_task) (j1 j2 : Job),
      job_task j1 = tsk_other → is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j t0 j1 →
      job_task j2 = tsk_other → is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j t0 j2 → j1 = j2) :
    ∀ (tsk_other : sporadic_task) (j0 : Job), job_task j0 = tsk_other → is_carry_in_job job_arrival job_cost job_task arr_seq num_cpus sched higher_eq_priority tsk j t0 j0 →
      carry_in_workload job_cost num_cpus sched j t0 j0 ≤ task_cost tsk_other - 1 := by
  intro tsk_other j0 htsk hci
  obtain ⟨harr, hhp, hlt, hnc⟩ := hci
  -- the carry-in job is pending at `t0 - 1`, which is not hp-busy, so it is scheduled there
  have hs := CaseStudies.Support.Common.carry_in_job_scheduled task_cost task_period task_deadline
    job_arrival job_cost job_task arr_seq ts sched higher_eq_priority H_sporadic_tasks
    H_valid_task_parameters H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
    H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_priority_transitive H_priority_antisymmetric H_work_conserving H_respects_FP_policy
    H_sequential_tasks tsk task_in_ts (t0 sched j) t0_left_boundary j0 harr hhp hlt hnc
  have h1 := CaseStudies.Support.Common.service_pos_of_scheduled sched j0 _ hs
  have hcost : job_cost j0 ≤ task_cost tsk_other := by
    have := (H_valid_job_parameters j0 harr).2.1
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [← htsk]; exact this
  have ht : t0 sched j - 1 + 1 = t0 sched j := by tomega
  rw [ht] at h1
  unfold carry_in_workload
  tomega

end CaseStudies.RTSS2009.Lemma1_2.ResponseTimeAnalysisFP

theorem CaseStudies.RTSS2009.Lemma1_2.solution : CaseStudies.RTSS2009.Lemma1_2.ResponseTimeAnalysisFP.Lemma1_09_statement.{u, v} :=
  @CaseStudies.RTSS2009.Lemma1_2.ResponseTimeAnalysisFP.Lemma1_09
