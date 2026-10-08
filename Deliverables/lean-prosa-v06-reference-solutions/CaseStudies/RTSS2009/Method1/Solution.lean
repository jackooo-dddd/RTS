import CaseStudies.RTSS2009.Method1.Statement
import CaseStudies.Support.Common

/-! Reference solution of benchmark task `2009-RTSS-Method1`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTSS2009.Method1.ResponseTimeAnalysisFP

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

theorem gn_method1 {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      higher_priority_task higher_eq_priority tsk hp_tsk = true → ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_hp_bounds_only_interfering_tasks : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → hp_tsk ∈ ts ∧ higher_priority_task higher_eq_priority tsk hp_tsk = true)
    (H_hp_bounds_uniq_tasks : (hp_bounds.map (fun p => p.1)).Nodup)
    (H_response_time_bounds_ge_cost : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds : R = task_cost tsk +
      div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus) num_cpus)
    (Huniq_hp_bounds : hp_bounds.Nodup)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (Method1_10_09 : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      (!completed job_cost sched j (job_arrival j + R)) = true →
      (∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk → job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) →
        (∃ (tsk_k : sporadic_task) (R_k : time), (tsk_k, R_k) ∈ CI_taskset task_cost task_period tsk hp_bounds R num_cpus ∧
          min (W task_cost task_period tsk_k R_k R) (R - task_cost tsk + 1) <
            min (task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) ∨
        (∃ (tsk_k : sporadic_task) (R_k : time), (tsk_k, R_k) ∈ NC_taskset task_cost task_period tsk hp_bounds R num_cpus ∧
          min (W_NC task_cost task_period tsk_k R) (R - task_cost tsk + 1) <
            min (task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)))
    (interference_bound_ci : ∀ (j : Job) (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ CI_taskset task_cost task_period tsk hp_bounds R num_cpus →
      task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R) ≤ W task_cost task_period tsk_other R_other R)
    (interference_bound_nc : ∀ (j : Job) (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ NC_taskset task_cost task_period tsk hp_bounds R num_cpus →
      task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R) ≤ W_NC task_cost task_period tsk_other R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  have key : ∀ n : Nat, ∀ j : Job, job_arrival j = n → arrives_in arr_seq j → job_task j = tsk →
      completed job_cost sched j (job_arrival j + R) = true := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro j hn harr htsk
      by_contra hnc
      have hprev : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
          job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true :=
        fun j0 h0 ht0 hlt => ih _ (hn ▸ hlt) j0 rfl h0 ht0
      rcases Method1_10_09 j harr htsk (by simpa using hnc) hprev with
        ⟨tk, Rk, hmem, hlt⟩ | ⟨tk, Rk, hmem, hlt⟩
      · have := interference_bound_ci j tk Rk hmem
        exact absurd hlt (Nat.not_lt.mpr (min_le_min_right _ this))
      · have := interference_bound_nc j tk Rk hmem
        exact absurd hlt (Nat.not_lt.mpr (min_le_min_right _ this))
  intro j harr htsk
  exact key _ j rfl harr htsk

end CaseStudies.RTSS2009.Method1.ResponseTimeAnalysisFP

theorem CaseStudies.RTSS2009.Method1.solution : CaseStudies.RTSS2009.Method1.ResponseTimeAnalysisFP.gn_method1_statement.{u, v} :=
  @CaseStudies.RTSS2009.Method1.ResponseTimeAnalysisFP.gn_method1
