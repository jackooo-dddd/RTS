-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/schedule.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
open Prosa.Util.Epsilon

section Definitions

variable {Task : Type _} [DecidableEq Task]
variable (task_cost : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)

variable (sched : schedule Job)

variable (job_lock_in_service : Job → Time)

def job_lock_in_service_positive : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_cost_positive job_cost j →
    0 < job_lock_in_service j

def job_lock_in_service_le_job_cost : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_cost_positive job_cost j →
    job_lock_in_service j ≤ job_cost j

def job_nonpreemptive_after_lock_in_service : Prop :=
  ∀ j t t',
    arrives_in arr_seq j →
    t ≤ t' →
    job_lock_in_service j ≤ service sched j t →
    ¬ completed_by job_cost sched j t' →
    scheduled_at sched j t' = true

def proper_job_lock_in_service : Prop :=
  (∀ j, arrives_in arr_seq j → job_cost_positive job_cost j → 0 < job_lock_in_service j) ∧
  (∀ j, arrives_in arr_seq j → job_cost_positive job_cost j → job_lock_in_service j ≤ job_cost j) ∧
  (∀ j t t', arrives_in arr_seq j → t ≤ t' → job_lock_in_service j ≤ service sched j t →
    ¬ completed_by job_cost sched j t' → scheduled_at sched j t' = true)

variable (task_lock_in_service : Task → Time)

def task_lock_in_service_le_task_cost (tsk : Task) : Prop :=
  task_lock_in_service tsk ≤ task_cost tsk

def task_lock_in_service_bounds_job_lock_in_service (tsk : Task) : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_lock_in_service j ≤ task_lock_in_service tsk

def proper_task_lock_in_service (tsk : Task) : Prop :=
  task_lock_in_service tsk ≤ task_cost tsk ∧
  (∀ j, arrives_in arr_seq j → job_task j = tsk → job_lock_in_service j ≤ task_lock_in_service tsk)

end Definitions

section Examples

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)

variable (arr_seq : arrival_sequence Job)

variable (sched : schedule Job)

variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

section FullyPreemptiveModel

private def job_lock_in_service_fp (job_cost : Job → Time) (j : Job) : Time := job_cost j

include H_completed_jobs_dont_execute in
theorem job_nonpreemptive_after_lock_in_service_trivial :
    job_nonpreemptive_after_lock_in_service job_cost arr_seq sched
      (job_lock_in_service_fp job_cost) := by
  intro j t t' _ hle hserv hncomp
  exfalso; apply hncomp
  exact completion_monotonic job_cost sched j t t' hle hserv

end FullyPreemptiveModel

section FullyNonPreemptiveModel

private def job_lock_in_service_np (_j : Job) : Time := ε

variable (H_is_nonpreemptive_schedule :
    is_nonpreemptive_schedule job_cost sched)

include H_completed_jobs_dont_execute H_is_nonpreemptive_schedule in
theorem property_last_segment_is_nonpreemptive_holds :
    job_nonpreemptive_after_lock_in_service job_cost arr_seq sched
      job_lock_in_service_np := by
  intro j t t' _ hle hserv hncomp
  have hserv_pos : 0 < service sched j t := by
    simp only [job_lock_in_service_np, ε] at hserv; exact Nat.lt_of_lt_of_le Nat.zero_lt_one hserv
  obtain ⟨ts, hts_lt, hsched_ts⟩ := scheduled_at_earlier_time sched j t hserv_pos
  exact H_is_nonpreemptive_schedule j ts t' (le_trans (le_of_lt hts_lt) hle) hsched_ts hncomp

end FullyNonPreemptiveModel

end Examples

end Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
