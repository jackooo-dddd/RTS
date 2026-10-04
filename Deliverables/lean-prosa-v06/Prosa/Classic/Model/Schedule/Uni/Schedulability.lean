-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/schedulability.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 71)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.ResponseTime

/-!
Deadline misses in uniprocessor schedules (Rocq module `Schedulability`).

Representation notes: Boolean tests in proposition position are `= true`; `tsk \in ts` is `tsk ∈ ts`; the
section-local `Let`s (`job_completed_by`, `response_time_bounded_by`) are unfolded. Binder lists follow the
Rocq contract (`task_completes_before_deadline` takes `task_deadline` and `H_job_deadline_eq_task_deadline` but
not `task_cost` nor `H_completed_jobs_dont_execute`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime

universe u v

def job_misses_no_deadline {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (sched : schedule Job) (j : Job) : Prop :=
  completed_by job_cost sched j (job_arrival j + job_deadline j) = true

def task_misses_no_deadline {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    {Task : Type v} [DecidableEq Task] (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (tsk : Task) : Prop :=
  ∀ j, arrives_in arr_seq j → job_task j = tsk → job_misses_no_deadline job_arrival job_cost job_deadline sched j

def taskset_misses_no_deadline {Job : Type u} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    {Task : Type v} [DecidableEq Task] (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (sched : schedule Job) (ts : List Task) : Prop :=
  ∀ tsk, tsk ∈ ts → task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

theorem task_completes_before_deadline {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) {Task : Type v} [DecidableEq Task] (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (task_deadline : Task → time)
    (H_job_deadline_eq_task_deadline : ∀ j, arrives_in arr_seq j →
      job_deadline_eq_task_deadline task_deadline job_deadline job_task j)
    (tsk : Task) (R : time) (H_R_le_deadline : R ≤ task_deadline tsk)
    (H_response_time_bounded : is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R) :
    task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  intro j ARRj JOBtsk
  have h := H_response_time_bounded j ARRj JOBtsk
  unfold is_response_time_bound_of_job at h
  have hd := H_job_deadline_eq_task_deadline j ARRj
  unfold job_deadline_eq_task_deadline at hd
  apply completion_monotonic job_cost sched j (job_arrival j + R)
  · rw [hd, JOBtsk]; exact Nat.add_le_add_left H_R_le_deadline _
  · exact h

end Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability
