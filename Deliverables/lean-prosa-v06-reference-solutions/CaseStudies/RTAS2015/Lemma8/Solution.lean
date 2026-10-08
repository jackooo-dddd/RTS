import CaseStudies.RTAS2015.Lemma8.Statement
import CaseStudies.Support.Common
import Prosa.Classic.Analysis.Apa.BertognaFpTheory

/-! Reference solution of benchmark task `2015-RTAS-Lemma8`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity
open Prosa.Classic.Model.Schedule.Apa.Interference.Interference
open Prosa.Classic.Model.Schedule.Apa.Platform.Platform
open Prosa.Classic.Util.DivMod (div_floor)
open Prosa.Util.Sum (sumFiltered)

theorem bertogna_cirinei_response_time_bound_fp
    {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    {num_cpus : Nat} (alpha : task_affinity sporadic_task num_cpus)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (higher_eq_priority : FP_policy sporadic_task)
    (H_respects_affinity : respects_affinity job_task sched alpha)
    (H_work_conserving : apa_work_conserving job_arrival job_cost job_task arr_seq sched alpha)
    (H_respects_FP_policy : respects_FP_policy_under_weak_APA job_arrival job_cost job_task arr_seq
      sched alpha higher_eq_priority)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (alpha' : task_affinity sporadic_task num_cpus)
    (H_affinity_subset : ∀ tsk0 : sporadic_task, tsk0 ∈ ts →
      is_subaffinity (alpha' tsk0) (alpha tsk0))
    (H_at_least_one_cpu : ∀ tsk0 : sporadic_task, tsk0 ∈ ts →
      0 < (Finset.univ.filter (fun x => x ∈ alpha' tsk0)).card)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds →
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks : ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
      higher_priority_task_in alpha higher_eq_priority tsk (alpha tsk) hp_tsk = true →
      ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (H_response_time_bounds_ge_cost : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → task_cost hp_tsk ≤ R)
    (H_interfering_tasks_miss_no_deadlines : ∀ (hp_tsk : sporadic_task) (R : time),
      (hp_tsk, R) ∈ hp_bounds → R ≤ task_deadline hp_tsk)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period task_deadline alpha tsk
          (alpha' tsk) hp_bounds R higher_eq_priority)
          (Finset.univ.filter (fun x => x ∈ alpha' tsk)).card)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  -- The case study's bound is the classic APA bound for the response-time bounds `d_k`:
  -- apply the classic theorem to `hp_bounds` with every bound replaced by the task's deadline.
  let hp' := hp_bounds.map (fun p => (p.1, task_deadline p.1))
  have hbound : total_interference_bound_fp task_cost task_period task_deadline alpha tsk
      (alpha' tsk) hp_bounds R higher_eq_priority =
      Prosa.Classic.Analysis.Apa.InterferenceBoundFp.InterferenceBoundFP.total_interference_bound_fp
        task_cost task_period alpha tsk (alpha' tsk) hp' R higher_eq_priority := by
    unfold total_interference_bound_fp
      Prosa.Classic.Analysis.Apa.InterferenceBoundFp.InterferenceBoundFP.total_interference_bound_fp
      sumFiltered
    simp only [hp', List.filter_map, List.map_map]
    rfl
  have hmem : ∀ k R', (k, R') ∈ hp' → ∃ R0, (k, R0) ∈ hp_bounds ∧ R' = task_deadline k := by
    intro k R' h
    obtain ⟨⟨k0, R0⟩, h0, he⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨R0, h0, rfl⟩
  refine Prosa.Classic.Analysis.Apa.BertognaFpTheory.ResponseTimeAnalysisFP.bertogna_cirinei_response_time_bound_fp
    task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq
    H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines
    H_all_jobs_from_taskset alpha sched H_jobs_come_from_arrival_sequence H_sequential_jobs
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority
    H_respects_affinity H_work_conserving H_respects_FP_policy tsk task_in_ts alpha'
    H_affinity_subset H_at_least_one_cpu hp' ?_ ?_ ?_ ?_ R ?_ H_response_time_no_larger_than_deadline
  · intro k R' h
    obtain ⟨R0, h0, rfl⟩ := hmem k R' h
    exact CaseStudies.Support.Common.rtb_mono (H_interfering_tasks_miss_no_deadlines k R0 h0)
      (H_response_time_of_interfering_tasks_is_known k R0 h0)
  · intro k hk hhp
    obtain ⟨R0, h0⟩ := H_hp_bounds_has_interfering_tasks k hk hhp
    exact ⟨task_deadline k, List.mem_map.mpr ⟨(k, R0), h0, rfl⟩⟩
  · intro k R' h
    obtain ⟨R0, h0, rfl⟩ := hmem k R' h
    exact le_trans (H_response_time_bounds_ge_cost k R0 h0) (H_interfering_tasks_miss_no_deadlines k R0 h0)
  · intro k R' h
    obtain ⟨R0, h0, rfl⟩ := hmem k R' h
    exact le_refl _
  · rw [← hbound]; exact H_response_time_recurrence_holds

end CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP

theorem CaseStudies.RTAS2015.Lemma8.solution : CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP.bertogna_cirinei_response_time_bound_fp_statement.{u, v} :=
  @CaseStudies.RTAS2015.Lemma8.ResponseTimeAnalysisFP.bertogna_cirinei_response_time_bound_fp
