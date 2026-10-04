-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/response_time.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 57)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedule

/-!
Response-time bounds in uniprocessor schedules (Rocq module `ResponseTime`).

Representation notes: Boolean tests in proposition position are `= true`; `\sum_(a <= t < b) F t` is
`∑ t ∈ Finset.Ico a b, F t`; the section-local `Let`s (`job_has_completed_by`, `response_time_bounded_by`) are
unfolded. Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def is_response_time_bound_of_job {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (j : Job) (R : time) : Bool :=
  completed_by job_cost sched j (job_arrival j + R)

def is_response_time_bound_of_task {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v}
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (tsk : sporadic_task) (R : time) : Prop :=
  ∀ j, arrives_in arr_seq j → job_task j = tsk → is_response_time_bound_of_job job_arrival job_cost sched j R = true

theorem service_after_job_rt_zero {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (j : Job) (R : time) (response_time_bound : is_response_time_bound_of_job job_arrival job_cost sched j R = true) :
    ∀ t' : Nat, job_arrival j + R ≤ t' → service_at sched j t' = 0 := by
  intro t' LE
  have COMP := completion_monotonic job_cost sched j _ t' LE response_time_bound
  have NS := completed_implies_not_scheduled job_cost sched j H_completed_jobs_dont_execute t' COMP
  simp only [Bool.not_eq_true'] at NS
  simp [service_at, NS]

theorem cumulative_service_after_job_rt_zero {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (sched : schedule Job) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (j : Job) (R : time) (response_time_bound : is_response_time_bound_of_job job_arrival job_cost sched j R = true) :
    ∀ t' t'' : Nat, job_arrival j + R ≤ t' → ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 := by
  intro t' t'' LE
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact service_after_job_rt_zero job_arrival job_cost sched H_completed_jobs_dont_execute j R response_time_bound i
    (by omega')

theorem service_after_task_rt_zero {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v}
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : sporadic_task) (R : time)
    (response_time_bound : is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R)
    (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j) (H_job_of_task : job_task j = tsk) :
    ∀ t' : Nat, job_arrival j + R ≤ t' → service_at sched j t' = 0 :=
  service_after_job_rt_zero job_arrival job_cost sched H_completed_jobs_dont_execute j R
    (response_time_bound j H_from_arrival_sequence H_job_of_task)

theorem cumulative_service_after_task_rt_zero {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v}
    [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : sporadic_task) (R : time)
    (response_time_bound : is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R)
    (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j) (H_job_of_task : job_task j = tsk) :
    ∀ t' t'' : Nat, job_arrival j + R ≤ t' → ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 :=
  cumulative_service_after_job_rt_zero job_arrival job_cost sched H_completed_jobs_dont_execute j R
    (response_time_bound j H_from_arrival_sequence H_job_of_task)

end Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
