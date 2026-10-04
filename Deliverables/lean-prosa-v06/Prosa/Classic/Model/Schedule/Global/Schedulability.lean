-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/global/schedulability.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 31)

import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.ResponseTime

/-!
Schedulability (Rocq module `Schedulability`).  Binder lists follow the Rocq
contract.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule

universe u v

def job_misses_no_deadline {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (j : Job) : Bool :=
  completed job_cost sched j (job_arrival j + job_deadline j)

def task_misses_no_deadline {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (tsk : sporadic_task) : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_misses_no_deadline job_arrival job_cost job_deadline sched j = true

def task_misses_no_deadline_before {sporadic_task : Type u} {Job : Type v}
    [DecidableEq sporadic_task] [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (tsk : sporadic_task) (t' : time) : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_arrival j + job_deadline j < t' →
    job_misses_no_deadline job_arrival job_cost job_deadline sched j = true

theorem service_after_job_deadline_zero {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job)
    (no_deadline_miss : job_misses_no_deadline job_arrival job_cost job_deadline sched j = true) :
    ∀ t' : time,
      job_arrival j + job_deadline j ≤ t' →
      service_at sched j t' = 0 :=
  Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.service_after_job_rt_zero
    job_arrival job_cost sched H_completed_jobs_dont_execute j (job_deadline j) no_deadline_miss

theorem cumulative_service_after_job_deadline_zero {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (j : Job)
    (no_deadline_miss : job_misses_no_deadline job_arrival job_cost job_deadline sched j = true) :
    ∀ t' t'' : time,
      job_arrival j + job_deadline j ≤ t' →
      ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 :=
  Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime.cumulative_service_after_job_rt_zero
    job_arrival job_cost sched H_completed_jobs_dont_execute j (job_deadline j) no_deadline_miss

theorem service_after_task_deadline_zero {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task)
    (no_deadline_misses :
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_task : job_task j = tsk)
    (H_valid_job : valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) :
    ∀ t' : time,
      job_arrival j + task_deadline tsk ≤ t' →
      service_at sched j t' = 0 := by
  intro t'
  have PARAMS1 := H_valid_job.2.2
  unfold job_deadline_eq_task_deadline at PARAMS1
  rw [← H_job_of_task, ← PARAMS1]
  exact service_after_job_deadline_zero job_arrival job_cost job_deadline sched
    H_completed_jobs_dont_execute j (no_deadline_misses j H_j_arrives H_job_of_task) t'

theorem cumulative_service_after_task_deadline_zero {sporadic_task : Type u}
    [DecidableEq sporadic_task] (task_cost task_deadline : sporadic_task → time) {Job : Type v}
    [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task)
    (no_deadline_misses :
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk)
    (j : Job) (H_j_arrives : arrives_in arr_seq j) (H_job_of_task : job_task j = tsk)
    (H_valid_job : valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) :
    ∀ t' t'' : time,
      job_arrival j + task_deadline tsk ≤ t' →
      ∑ t ∈ Finset.Ico t' t'', service_at sched j t = 0 := by
  intro t' t''
  have PARAMS1 := H_valid_job.2.2
  unfold job_deadline_eq_task_deadline at PARAMS1
  rw [← H_job_of_task, ← PARAMS1]
  exact cumulative_service_after_job_deadline_zero job_arrival job_cost job_deadline sched
    H_completed_jobs_dont_execute j (no_deadline_misses j H_j_arrives H_job_of_task) t' t''

end Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
