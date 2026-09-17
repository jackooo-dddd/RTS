-- Translated from: ../rt-proofs/classic/model/schedule/uni/workload.v
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Priority
import Mathlib.Data.List.Basic

namespace Prosa.Classic.Model.Schedule.Uni.Workload

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority

section WorkloadDefs

  variable {Task : Type _} [DecidableEq Task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : arrival_sequence Job)

  variable (jobs : List Job)

  section WorkloadOfJobs

    variable (P : Job → Bool)

    def workload_of_jobs := (jobs.filter P).map job_cost |>.sum

  end WorkloadOfJobs

  section PerTaskPriority

    variable (higher_eq_priority : FP_policy Task)
    variable (tsk : Task)

    def workload_of_higher_or_equal_priority_tasks :=
      workload_of_jobs job_cost jobs (fun j => higher_eq_priority (job_task j) tsk)

  end PerTaskPriority

  section PerJobPriority

    variable (higher_eq_priority : JLFP_policy Job)
    variable (j : Job)

    def workload_of_higher_or_equal_priority_jobs :=
      workload_of_jobs job_cost jobs (fun j_hp => higher_eq_priority j_hp j)

  end PerJobPriority

end WorkloadDefs

section TaskWorkload

  variable {Task : Type _} [DecidableEq Task]
  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : arrival_sequence Job)

  variable (tsk : Task)

  def task_workload (jobs : List Job) :=
    workload_of_jobs job_cost jobs (fun j => decide (job_task j = tsk))

  def task_workload_between (t1 t2 : Time) :=
    task_workload job_cost job_task tsk (jobs_arrived_between arr_seq t1 t2)

end TaskWorkload

section BasicLemmas

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)

  variable (arr_seq : arrival_sequence Job)

  theorem workload_of_jobs_cat (t t1 t2 : Time) (P : Job → Bool)
      (h : t1 ≤ t ∧ t ≤ t2) :
      workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2) P =
      workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t) P
      + workload_of_jobs job_cost (jobs_arrived_between arr_seq t t2) P := by
    obtain ⟨h1, h2⟩ := h
    have h1' : workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2) P =
      List.sum (List.map job_cost (List.filter P (jobs_arrived_between arr_seq t1 t2))) := rfl
    have h2' : workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t) P =
      List.sum (List.map job_cost (List.filter P (jobs_arrived_between arr_seq t1 t))) := rfl
    have h3' : workload_of_jobs job_cost (jobs_arrived_between arr_seq t t2) P =
      List.sum (List.map job_cost (List.filter P (jobs_arrived_between arr_seq t t2))) := rfl
    rw [h1', h2', h3']
    rw [job_arrived_between_cat arr_seq t1 t t2 h1 h2,
      List.filter_append, List.map_append, List.sum_append]

end BasicLemmas

end Prosa.Classic.Model.Schedule.Uni.Workload
