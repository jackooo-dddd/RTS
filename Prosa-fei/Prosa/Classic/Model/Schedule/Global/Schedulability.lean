-- Translated from: ../rt-proofs/classic/model/schedule/global/schedulability.v
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Global.Schedulability

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Schedule

namespace Schedulability

section SchedulableDefs

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

section ScheduleOfJobs

variable (j : Job)

def job_misses_no_deadline : Prop :=
  completed job_cost sched j (job_arrival j + job_deadline j)

end ScheduleOfJobs

section ScheduleOfTasks

variable (tsk : sporadic_task)

def task_misses_no_deadline : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_misses_no_deadline job_arrival job_cost job_deadline sched j

def task_misses_no_deadline_before (t' : Time) : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_arrival j + job_deadline j < t' →
    job_misses_no_deadline job_arrival job_cost job_deadline sched j

end ScheduleOfTasks

end SchedulableDefs

section BasicLemmas

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
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

section SpecificJob

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (no_deadline_miss : job_misses_no_deadline job_arrival job_cost job_deadline sched j)
include H_completed_jobs_dont_execute no_deadline_miss

theorem service_after_job_deadline_zero :
    ∀ t',
      t' ≥ job_arrival j + job_deadline j →
      service_at sched j t' = 0 := by
  intro t' h_le
  have h_comp : completed job_cost sched j t' :=
    completion_monotonic job_cost sched j H_completed_jobs_dont_execute
      (job_arrival j + job_deadline j) t' h_le no_deadline_miss
  have h_not_sched : ¬ scheduled sched j t' :=
    completed_implies_not_scheduled job_cost sched j H_completed_jobs_dont_execute t' h_comp
  exact (not_scheduled_no_service sched j t').mp h_not_sched

theorem cumulative_service_after_job_deadline_zero :
    ∀ t' t'',
      t' ≥ job_arrival j + job_deadline j →
      ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 := by
  intro t' t'' h_le
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_Ico] at ht
  exact service_after_job_deadline_zero job_arrival job_cost job_deadline sched
    H_completed_jobs_dont_execute j no_deadline_miss t (le_trans h_le ht.1)

end SpecificJob

section AllJobs

variable (tsk : sporadic_task)
variable (no_deadline_misses :
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk)
variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_task : job_task j = tsk)
variable (H_valid_job :
  valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
include H_completed_jobs_dont_execute no_deadline_misses H_j_arrives H_job_of_task H_valid_job

theorem service_after_task_deadline_zero :
    ∀ t',
      t' ≥ job_arrival j + task_deadline tsk →
      service_at sched j t' = 0 := by
  intro t' h_le
  have h_valid := H_valid_job
  unfold valid_sporadic_job at h_valid
  obtain ⟨_, _, h_dl_eq⟩ := h_valid
  unfold job_deadline_eq_task_deadline at h_dl_eq
  rw [H_job_of_task] at h_dl_eq
  have h_no_miss : job_misses_no_deadline job_arrival job_cost job_deadline sched j :=
    no_deadline_misses j H_j_arrives H_job_of_task
  exact service_after_job_deadline_zero job_arrival job_cost job_deadline sched
    H_completed_jobs_dont_execute j h_no_miss t' (by rw [h_dl_eq]; exact h_le)

theorem cumulative_service_after_task_deadline_zero :
    ∀ t' t'',
      t' ≥ job_arrival j + task_deadline tsk →
      ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 := by
  intro t' t'' h_le
  have h_valid := H_valid_job
  unfold valid_sporadic_job at h_valid
  obtain ⟨_, _, h_dl_eq⟩ := h_valid
  unfold job_deadline_eq_task_deadline at h_dl_eq
  rw [H_job_of_task] at h_dl_eq
  have h_no_miss : job_misses_no_deadline job_arrival job_cost job_deadline sched j :=
    no_deadline_misses j H_j_arrives H_job_of_task
  exact cumulative_service_after_job_deadline_zero job_arrival job_cost job_deadline sched
    H_completed_jobs_dont_execute j h_no_miss t' t'' (by rw [h_dl_eq]; exact h_le)

end AllJobs

end BasicLemmas

end Schedulability

end Prosa.Classic.Model.Schedule.Global.Schedulability
