import CaseStudies.RTSS2009.Extend1_10.Statement
import CaseStudies.Support.Common

/-! Reference solution of benchmark task `2009-RTSS-Extend1_10`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTSS2009.Extend1_10.ResponseTimeAnalysisFP

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

/-- LEAN_HELPER: the higher-priority bounds are a permutation of the carry-in set followed by the no-carry-in set. -/
theorem perm_CI_NC {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_prev : List (sporadic_task × time))
    (delta : time) (num_cpus : Nat) (hnd : R_prev.Nodup) :
    R_prev.Perm (CI_taskset task_cost task_period tsk R_prev delta num_cpus ++
      NC_taskset task_cost task_period tsk R_prev delta num_cpus) := by
  unfold NC_taskset CI_taskset
  convert CaseStudies.Support.Common.perm_take_append_filter (List.mergeSort_perm _ _) hnd (num_cpus - 1)

theorem Method1_10_09 {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_previous_jobs_of_tsk_completed : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true)
    (tsk_other : sporadic_task) (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ hp_bounds)
    (Method1_9 : total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus <
      sumSeq hp_bounds (fun (tsk_k, _) =>
        min (task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1))) :
    (∃ (tsk_k : sporadic_task) (R_k : time), (tsk_k, R_k) ∈ CI_taskset task_cost task_period tsk hp_bounds R num_cpus ∧
          min (W task_cost task_period tsk_k R_k R) (R - task_cost tsk + 1) <
            min (task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) ∨
        (∃ (tsk_k : sporadic_task) (R_k : time), (tsk_k, R_k) ∈ NC_taskset task_cost task_period tsk hp_bounds R num_cpus ∧
          min (W_NC task_cost task_period tsk_k R) (R - task_cost tsk + 1) <
            min (task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) (R - task_cost tsk + 1)) := by
  by_contra hneg
  simp only [not_or, not_exists, not_and, not_lt] at hneg
  obtain ⟨hCI, hNC⟩ := hneg
  let F : sporadic_task × time → Nat := fun p =>
    min (task_interference job_arrival job_cost job_task sched j p.1 (job_arrival j) (job_arrival j + R))
      (R - task_cost tsk + 1)
  have hperm := perm_CI_NC task_cost task_period tsk hp_bounds R num_cpus Huniq_hp_bounds
  have hsum : sumSeq hp_bounds F =
      sumSeq (CI_taskset task_cost task_period tsk hp_bounds R num_cpus) F +
        sumSeq (NC_taskset task_cost task_period tsk hp_bounds R num_cpus) F := by
    rw [CaseStudies.Support.Common.sumSeq_perm F hperm, CaseStudies.Support.Common.sumSeq_append]
  have hci := CaseStudies.Support.Common.sumSeq_le_sumSeq (CI_taskset task_cost task_period tsk hp_bounds R num_cpus) F
    (fun p => interference_bound_generic task_cost task_period tsk R p)
    (fun p hp => by obtain ⟨a, b⟩ := p; exact hCI a b hp)
  have hnc := CaseStudies.Support.Common.sumSeq_le_sumSeq (NC_taskset task_cost task_period tsk hp_bounds R num_cpus) F
    (fun p => interference_bound_nc task_cost task_period tsk R p)
    (fun p hp => by obtain ⟨a, b⟩ := p; exact hNC a b hp)
  have hgn : total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus =
      sumSeq (NC_taskset task_cost task_period tsk hp_bounds R num_cpus)
          (fun p => interference_bound_nc task_cost task_period tsk R p) +
        sumSeq (CI_taskset task_cost task_period tsk hp_bounds R num_cpus)
          (fun p => interference_bound_generic task_cost task_period tsk R p) := rfl
  have h9 : total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus < sumSeq hp_bounds F :=
    Method1_9
  omega

end CaseStudies.RTSS2009.Extend1_10.ResponseTimeAnalysisFP

theorem CaseStudies.RTSS2009.Extend1_10.solution : CaseStudies.RTSS2009.Extend1_10.ResponseTimeAnalysisFP.Method1_10_09_statement.{u, v} :=
  @CaseStudies.RTSS2009.Extend1_10.ResponseTimeAnalysisFP.Method1_10_09
