import CaseStudies.ECRTS2005.Lemma3
import Solutions.Support.Common

/-! Reference solution of benchmark task `2005-ECRTS-Lemma3`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Util.Sum (sumFiltered)

theorem Lemma3_05 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat) (sched : schedule Job num_cpus)
    (H_edf_policy : respects_JLFP_policy job_arrival job_cost arr_seq sched
      (EDF job_arrival job_deadline))
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_sequential_jobs : sequential_jobs sched)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_constrained_deadlines : ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (tsk : sporadic_task) (task_in_ts : tsk ∈ ts)
    (H_previous_jobs_of_tsk_completed : ∀ (j0 : Job) (t : Nat) (j : Job),
      arrives_in arr_seq j0 → arrives_in arr_seq j → job_task j0 = tsk → job_task j = tsk →
      job_arrival j0 < job_arrival j → job_arrival j ≤ t → completed job_cost sched j0 t = true)
    :
    ∀ (j : Job) (a b : time), arrives_in arr_seq j → job_task j = tsk →
      cumulative_task_interference job_arrival job_cost job_task ts num_cpus sched tsk j a b =
        num_cpus * total_interference job_arrival job_cost sched j a b := by
  intro j a b harr htsk
  -- at a backlogged instant every processor runs a job of a task of `ts` other than `tsk`
  apply Solutions.Support.Common.sum_task_interference_eq job_arrival job_cost job_task sched _
    (ts.nodup.filter _) j a b
  intro t _ _ hb cpu
  obtain ⟨j', hj'⟩ := H_work_conserving j t harr hb cpu
  have hs' : sched cpu t = some j' := by simpa [scheduled_on] using hj'
  have S' : scheduled sched j' t = true := by
    simp only [scheduled, List.any_eq_true, List.mem_finRange, true_and]
    exact ⟨cpu, hj'⟩
  have A' := H_jobs_come_from_arrival_sequence j' t S'
  refine ⟨j', hs', List.mem_filter.mpr ⟨H_all_jobs_from_taskset j' A', ?_⟩⟩
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  intro hsame
  have hpend' := scheduled_implies_pending job_arrival job_cost sched j'
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute t S'
  have hback := hb
  simp only [backlogged, pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true'] at hback
  obtain ⟨⟨harrj, _⟩, hnsj⟩ := hback
  have hne : j' ≠ j := by
    rintro rfl; rw [S'] at hnsj; exact Bool.noConfusion hnsj
  rcases lt_trichotomy (job_arrival j') (job_arrival j) with h | h | h
  · -- an earlier job of `tsk` is complete
    have hc := H_previous_jobs_of_tsk_completed j' t j A' harr hsame htsk h harrj
    simp [pending, hc] at hpend'
  · -- two jobs of `tsk` cannot arrive together
    have hp : 0 < task_period (job_task j') := by
      have := (H_valid_task_parameters _ (H_all_jobs_from_taskset j' A')).2.1
      simpa [Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask.task_period_positive] using this
    have := H_sporadic_tasks j' j hne A' harr (hsame.trans htsk.symm) (le_of_eq h)
    tomega
  · -- a later job of `tsk` has a later absolute deadline
    have hedf := H_edf_policy j j' t harr hb S'
    simp only [EDF, decide_eq_true_eq] at hedf
    have hd' : job_deadline j' = task_deadline tsk := by
      rw [← hsame]; exact (H_valid_job_parameters j' A').2.2
    have hd : job_deadline j = task_deadline tsk := by
      rw [← htsk]; exact (H_valid_job_parameters j harr).2.2
    tomega

end CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF

theorem Solutions.ECRTS2005.Lemma3.solution : CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF.Lemma3_05_statement.{u, v} :=
  @CaseStudies.ECRTS2005.Lemma3.ResponseTimeAnalysisEDF.Lemma3_05
