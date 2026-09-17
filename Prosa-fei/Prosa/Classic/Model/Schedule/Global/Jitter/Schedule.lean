-- Translated from: ../rt-proofs/classic/model/schedule/global/jitter/schedule.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Global.Jitter.Schedule

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Jitter.Job

namespace ScheduleWithJitter

section ArrivalDependentProperties

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_jitter : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

section JobProperties

variable (j : Job)

def actual_arrival := job_arrival j + job_jitter j

def jitter_has_passed (t : Time) := actual_arrival job_arrival job_jitter j ≤ t

def actual_arrival_before (t : Time) := actual_arrival job_arrival job_jitter j < t

def pending (t : Time) :=
  jitter_has_passed job_arrival job_jitter j t ∧ ¬ completed job_cost sched j t

def backlogged (t : Time) :=
  pending job_arrival job_cost job_jitter sched j t ∧ ¬ scheduled sched j t

end JobProperties

section ScheduleProperties

def jobs_execute_after_jitter :=
  ∀ j t, scheduled sched j t → jitter_has_passed job_arrival job_jitter j t

end ScheduleProperties

section BasicLemmas

variable (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
include H_jobs_execute_after_jitter

section Pending

variable (H_completed_jobs : completed_jobs_dont_execute job_cost sched)
include H_completed_jobs

theorem scheduled_implies_pending :
    ∀ j t,
      scheduled sched j t →
      pending job_arrival job_cost job_jitter sched j t := by
  intro j t h_sched
  unfold pending
  constructor
  · exact H_jobs_execute_after_jitter j t h_sched
  · intro h_comp
    have h_bound := H_completed_jobs j (t + 1)
    unfold service at h_bound
    rw [Finset.sum_Ico_succ_top (Nat.zero_le t)] at h_bound
    have h_serv_pos : service_at sched j t ≠ 0 := by
      intro h_eq
      exact ((not_scheduled_no_service sched j t).mpr h_eq) h_sched
    unfold completed service at h_comp
    have h_serv_ge : service_at sched j t ≥ 1 := Nat.one_le_iff_ne_zero.mpr h_serv_pos
    linarith

end Pending

section Service

theorem arrival_before_jitter :
    jobs_must_arrive_to_execute job_arrival sched := by
  intro j t h_sched
  show has_arrived job_arrival j t
  unfold has_arrived
  have h_jitter := H_jobs_execute_after_jitter j t h_sched
  unfold jitter_has_passed actual_arrival at h_jitter
  exact le_trans (Nat.le_add_right _ _) h_jitter

theorem service_before_jitter_zero :
    ∀ j t,
      t < job_arrival j + job_jitter j →
      service_at sched j t = 0 := by
  intro j t h_lt
  rw [← not_scheduled_no_service sched j t]
  intro h_sched
  have h_jitter := H_jobs_execute_after_jitter j t h_sched
  simp only [jitter_has_passed, actual_arrival] at h_jitter
  exact absurd h_lt (not_lt.mpr h_jitter)

theorem cumulative_service_before_jitter_zero :
    ∀ j t1 t2,
      t2 ≤ job_arrival j + job_jitter j →
      ∑ t ∈ Finset.Ico t1 t2, service_at sched j t = 0 := by
  intro j t1 t2 h_le
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_Ico] at ht
  exact service_before_jitter_zero job_arrival job_jitter sched H_jobs_execute_after_jitter j t (Nat.lt_of_lt_of_le ht.2 h_le)

end Service

end BasicLemmas

end ArrivalDependentProperties

end ScheduleWithJitter

namespace ScheduleOfSporadicTaskWithJitter

open ScheduleWithJitter
open Schedule

section ScheduledJobs

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_task : Job → sporadic_task)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (tsk : sporadic_task)

def task_scheduled_on (cpu : processor num_cpus) (t : Time) : Bool :=
  match sched cpu t with
  | some j => decide (job_task j = tsk)
  | none => false

def task_is_scheduled (t : Time) : Prop :=
  ∃ cpu : processor num_cpus, task_scheduled_on job_task sched tsk cpu t = true

def jobs_of_task_scheduled_between (t1 t2 : Time) : List Job :=
  (jobs_scheduled_between sched t1 t2).filter (fun j => decide (job_task j = tsk))

end ScheduledJobs

section ScheduleProperties

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable {Job : Type _} [DecidableEq Job]
variable (job_cost : Job → Time)
variable (job_jitter : Job → Time)
variable (job_task : Job → sporadic_task)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)

def jobs_of_same_task_dont_execute_in_parallel :=
  ∀ j j' t,
    job_task j = job_task j' →
    scheduled sched j t →
    scheduled sched j' t →
    j = j'

end ScheduleProperties

section BasicLemmas

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)
variable {Job : Type _} [DecidableEq Job]
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)
variable (arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence Job)
variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (jobs_dont_execute_after_completion : completed_jobs_dont_execute job_cost sched)
variable (tsk : sporadic_task)
variable (j : Job)
variable (H_j_arrives : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j)
variable (H_job_of_task : job_task j = tsk)
variable (valid_job :
  valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
include jobs_dont_execute_after_completion H_job_of_task valid_job

theorem cumulative_service_le_task_cost :
    ∀ t t',
      service_during sched j t t' ≤ task_cost tsk := by
  intro t t'
  have h_le_job := Schedule.cumulative_service_le_job_cost job_cost sched j jobs_dont_execute_after_completion t t'
  have h_valid := valid_job
  unfold Prosa.Classic.Model.Arrival.Basic.Job.valid_sporadic_job at h_valid
  obtain ⟨_, h_cost_le, _⟩ := h_valid
  unfold Prosa.Classic.Model.Arrival.Basic.Job.job_cost_le_task_cost at h_cost_le
  rw [H_job_of_task] at h_cost_le
  exact le_trans h_le_job h_cost_le

end BasicLemmas

end ScheduleOfSporadicTaskWithJitter

end Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
