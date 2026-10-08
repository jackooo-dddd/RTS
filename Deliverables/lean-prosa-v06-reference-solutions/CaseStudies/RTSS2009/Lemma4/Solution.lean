import CaseStudies.RTSS2009.Lemma4.Statement
import CaseStudies.Support.Common

/-! Reference solution of benchmark task `2009-RTSS-Lemma4`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTSS2009.Lemma4.ResponseTimeAnalysisFP

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

theorem Lemma4_09 {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (H_response_time_bounds_ge_cost : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds : R = task_cost tsk + div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds R num_cpus) num_cpus)
    (Huniq_hp_bounds : hp_bounds.Nodup)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job) (t0 : schedule Job num_cpus → Job → time)
    (t0_leq_arrival_time : t0 sched j ≤ job_arrival j)
    (cpu_busy_during_t0_rk : ∀ t : Nat, (decide (t0 sched j ≤ t) && decide (t < job_arrival j)) = true →
      hp_busy job_task ts num_cpus sched higher_eq_priority tsk t)
    (t0_left_boundary : t0 sched j = 0 ∨ ¬ hp_busy job_task ts num_cpus sched higher_eq_priority tsk (t0 sched j - 1))
    (H_j_arrives : arrives_in arr_seq j) (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
      job_arrival j0 < job_arrival j → completed job_cost sched j0 (job_arrival j0 + R) = true)
    (j_has_worstcase_responsetime : ∀ (j0 : Job) (x : Nat), arrives_in arr_seq j0 → job_task j0 = tsk →
      completed job_cost sched j (job_arrival j + x) = true →
      completed job_cost sched j0 (job_arrival j0 + x) = true)
    (chi : time)
    (chi_is_least_solution : ∀ x : time, x = task_cost tsk + div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds x num_cpus) num_cpus → chi ≤ x)
    (f : time)
    (f_is_finish_time : ((!completed job_cost sched j (f - 1)) && completed job_cost sched j f) = true)
    (arrival_before_finish : job_arrival j < f)
    (chi_is_solution : chi = task_cost tsk + div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds chi num_cpus) num_cpus)
    (phi_le_chi : job_arrival j - t0 sched j ≤ chi)
    (Lemma3 : ∀ t : Nat, t < f - t0 sched j → task_cost tsk ≤ t →
      t - task_cost tsk < div_floor (total_interference_bound_gn task_cost task_period tsk hp_bounds t num_cpus) num_cpus) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (chi - (job_arrival j - t0 sched j)) := by
  have hfin : completed job_cost sched j f = true := by
    simp only [Bool.and_eq_true] at f_is_finish_time; exact f_is_finish_time.2
  have hchi_e : task_cost tsk ≤ chi := by
    have := chi_is_solution; tomega
  have hf : f - t0 sched j ≤ chi := by
    by_contra hlt
    have h3 := Lemma3 chi (by tomega) hchi_e
    have := chi_is_solution
    tomega
  intro j0 harr htsk
  apply j_has_worstcase_responsetime j0 _ harr htsk
  exact completion_monotonic job_cost sched j f _ (by tomega) hfin

end CaseStudies.RTSS2009.Lemma4.ResponseTimeAnalysisFP

theorem CaseStudies.RTSS2009.Lemma4.solution : CaseStudies.RTSS2009.Lemma4.ResponseTimeAnalysisFP.Lemma4_09_statement.{u, v} :=
  @CaseStudies.RTSS2009.Lemma4.ResponseTimeAnalysisFP.Lemma4_09
