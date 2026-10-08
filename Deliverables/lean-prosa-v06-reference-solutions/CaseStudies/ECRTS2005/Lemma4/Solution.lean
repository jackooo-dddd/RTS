import CaseStudies.ECRTS2005.Lemma4.Statement
import CaseStudies.Support.Common

/-! Reference solution of benchmark task `2005-ECRTS-Lemma4`. -/

set_option linter.unusedVariables false

universe u v

namespace CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF

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

theorem Lemma4_05 {sporadic_task : Type u} [DecidableEq sporadic_task]
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
    (H_sequential_tasks : ∀ (j1 j2 : Job) (t : time) (cpu : processor num_cpus),
      arrives_in arr_seq j1 → arrives_in arr_seq j2 → job_task j1 = job_task j2 →
      job_arrival j1 < job_arrival j2 → scheduled_on sched j2 cpu t = true →
      completed job_cost sched j1 t = true)
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
    (Lemma_05 : ∀ (j : Job) (a b : time), arrives_in arr_seq j → job_task j = tsk →
        cumulative_task_interference job_arrival job_cost job_task ts num_cpus sched tsk j a b =
          num_cpus * total_interference job_arrival job_cost sched j a b) :
    ∀ (j : Job) (a b : time) (c : Nat), arrives_in arr_seq j → job_task j = tsk →
      (c ≤ total_interference job_arrival job_cost sched j a b ↔
        num_cpus * c ≤ sumFiltered ts.val (fun t => !decide (t = tsk))
          (fun t => min (task_interference job_arrival job_cost job_task sched j t a b) c)) := by
  intro j a b c harr htsk
  have hsum := Lemma_05 j a b harr htsk
  unfold cumulative_task_interference at hsum
  have hle : ∀ k, task_interference job_arrival job_cost job_task sched j k a b ≤
      total_interference job_arrival job_cost sched j a b :=
    fun k => CaseStudies.Support.Common.task_interference_le_total task_cost task_period task_deadline
      job_arrival job_cost job_task arr_seq ts sched H_sporadic_tasks H_valid_task_parameters
      H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_sequential_jobs
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_tasks j k a b
  constructor
  · intro hc
    exact CaseStudies.Support.Common.sum_min_ge (ts.val.filter (fun t => !decide (t = tsk)))
      (fun k => task_interference job_arrival job_cost job_task sched j k a b) num_cpus
      (total_interference job_arrival job_cost sched j a b) c hsum (fun k _ => hle k) hc
  · intro h
    by_contra hlt
    have hmin := CaseStudies.Support.Common.sumSeq_le_sumSeq (ts.val.filter (fun t => !decide (t = tsk)))
      (fun k => min (task_interference job_arrival job_cost job_task sched j k a b) c)
      (fun k => task_interference job_arrival job_cost job_task sched j k a b)
      (fun k _ => min_le_left _ _)
    have h1 : num_cpus * c ≤ num_cpus * total_interference job_arrival job_cost sched j a b :=
      le_trans h (le_trans hmin (le_of_eq hsum))
    exact hlt (Nat.le_of_mul_le_mul_left h1 H_at_least_one_cpu)

end CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF

theorem CaseStudies.ECRTS2005.Lemma4.solution : CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF.Lemma4_05_statement.{u, v} :=
  @CaseStudies.ECRTS2005.Lemma4.ResponseTimeAnalysisEDF.Lemma4_05
