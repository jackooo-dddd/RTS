-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/response_time.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 30)

import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule

/-!
Response-time bounds (Rocq module `ResponseTime`).  The section-local
`job_has_completed_by := completed job_cost sched` is unfolded.  Binder lists
follow the Rocq contract (e.g. `service_after_job_rt_zero` does not take
`H_j_arrives`; the task-level lemmas do).
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule

universe u v

def is_response_time_bound_of_task {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (tsk : sporadic_task) (R : time) : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    completed job_cost sched j (job_arrival j + R) = true

theorem service_after_job_rt_zero {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (j : Job) (R : time)
    (response_time_bound : completed job_cost sched j (job_arrival j + R) = true) :
    ∀ t' : time,
      job_arrival j + R ≤ t' →
      service_at sched j t' = 0 := by
  intro t' LE
  have RT := completion_monotonic job_cost sched j _ t' LE response_time_bound
  have NS := completed_implies_not_scheduled job_cost sched j H_completed_jobs_dont_execute t' RT
  rw [not_scheduled_no_service] at NS
  simpa using NS

theorem cumulative_service_after_job_rt_zero {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (j : Job) (R : time)
    (response_time_bound : completed job_cost sched j (job_arrival j + R) = true) :
    ∀ t' t'' : time,
      job_arrival j + R ≤ t' →
      ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 := by
  intro t' t'' LE
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_Ico] at hi
  exact service_after_job_rt_zero job_arrival job_cost sched H_completed_jobs_dont_execute j R
    response_time_bound i (Nat.le_trans LE hi.1)

theorem service_after_task_rt_zero {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (R : time)
    (response_time_bound :
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_task : job_task j = tsk) :
    ∀ t' : time,
      job_arrival j + R ≤ t' →
      service_at sched j t' = 0 :=
  service_after_job_rt_zero job_arrival job_cost sched H_completed_jobs_dont_execute j R
    (response_time_bound j H_j_arrives H_job_of_task)

theorem cumulative_service_after_task_rt_zero {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (R : time)
    (response_time_bound :
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_task : job_task j = tsk) :
    ∀ t' t'' : time,
      job_arrival j + R ≤ t' →
      ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 :=
  cumulative_service_after_job_rt_zero job_arrival job_cost sched H_completed_jobs_dont_execute j R
    (response_time_bound j H_j_arrives H_job_of_task)

end Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
