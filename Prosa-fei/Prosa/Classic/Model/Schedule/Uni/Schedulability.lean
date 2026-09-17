-- Translated from: ../rt-proofs/classic/model/schedule/uni/schedulability.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Schedulability

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

section ScheduleDefs

variable (Job : Type _) [DecidableEq Job]

def schedule := Time → Option Job

end ScheduleDefs

section ScheduleProperties

variable {Job : Type _} [DecidableEq Job]
variable (job_cost : Job → Time)
variable (sched : schedule Job)

def scheduled_at (j : Job) (t : Time) : Bool :=
  sched t == some j

def service_at (j : Job) (t : Time) : Nat :=
  if scheduled_at sched j t then 1 else 0

def service_during (j : Job) (t1 t2 : Time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, service_at sched j t

def service (j : Job) (t : Time) : Nat :=
  service_during sched j 0 t

def completed_by (j : Job) (t : Time) : Prop :=
  job_cost j ≤ service sched j t

def completed_jobs_dont_execute : Prop :=
  ∀ j t, service sched j t ≤ job_cost j

theorem completion_monotonic (j : Job) (t t' : Time)
    (h_le : t ≤ t')
    (h_comp : completed_by job_cost sched j t) :
    completed_by job_cost sched j t' := by
  unfold completed_by service service_during at *
  calc job_cost j ≤ ∑ t_1 ∈ Finset.Ico 0 t, service_at sched j t_1 := h_comp
    _ ≤ ∑ t_1 ∈ Finset.Ico 0 t', service_at sched j t_1 := by
        apply Finset.sum_le_sum_of_subset
        exact Finset.Ico_subset_Ico_right h_le

end ScheduleProperties

section ResponseTimeBound

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)

variable {Task : Type _} [DecidableEq Task]
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)
variable (sched : schedule Job)

def is_response_time_bound_of_job (j : Job) (R : Time) : Prop :=
  completed_by job_cost sched j (job_arrival j + R)

def is_response_time_bound_of_task (tsk : Task) (R : Time) : Prop :=
  ∀ j, arrives_in arr_seq j →
    job_task j = tsk →
    is_response_time_bound_of_job job_arrival job_cost sched j R

end ResponseTimeBound

section DeadlineMisses

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)

variable {Task : Type _} [DecidableEq Task]
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)
variable (sched : schedule Job)

section Definitions

section JobLevel

variable (j : Job)

def job_misses_no_deadline : Prop :=
  completed_by job_cost sched j (job_arrival j + job_deadline j)

end JobLevel

section TaskLevel

variable (tsk : Task)

def task_misses_no_deadline : Prop :=
  ∀ j, arrives_in arr_seq j →
    job_task j = tsk →
    job_misses_no_deadline job_arrival job_cost job_deadline sched j

end TaskLevel

section TaskSetLevel

variable (ts : List Task)

def taskset_misses_no_deadline : Prop :=
  ∀ tsk, tsk ∈ ts →
    task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

end TaskSetLevel

end Definitions

section Lemmas

variable (task_cost : Task → Time)
variable (task_deadline : Task → Time)

section ResponseTimeIsBounded

variable (H_job_deadline_eq_task_deadline :
  ∀ j, arrives_in arr_seq j →
    job_deadline j = task_deadline (job_task j))

variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (tsk : Task)

variable (R : Time)
variable (H_R_le_deadline : R ≤ task_deadline tsk)
variable (H_response_time_bounded :
  is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R)

include H_job_deadline_eq_task_deadline H_completed_jobs_dont_execute H_R_le_deadline H_response_time_bounded

theorem task_completes_before_deadline :
    task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  intro j h_arrives h_task
  unfold job_misses_no_deadline
  apply completion_monotonic job_cost sched j (job_arrival j + R)
  · rw [Nat.add_le_add_iff_left]
    calc R ≤ task_deadline tsk := H_R_le_deadline
      _ = task_deadline (job_task j) := by rw [h_task]
      _ = job_deadline j := by rw [H_job_deadline_eq_task_deadline j h_arrives]
  · exact H_response_time_bounded j h_arrives h_task

end ResponseTimeIsBounded

end Lemmas

end DeadlineMisses

end Prosa.Classic.Model.Schedule.Uni.Schedulability
