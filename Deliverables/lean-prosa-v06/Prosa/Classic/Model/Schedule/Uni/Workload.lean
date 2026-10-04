-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/workload.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 61)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority

/-!
Workload of sets of jobs (Rocq module `Workload`, uniprocessor model).

Representation notes: `\sum_(j <- jobs | P j) F j` is `sumFiltered jobs P F`; `job_task j == tsk` is
`decide (job_task j = tsk)`; Boolean chains `t1 <= t <= t2` in proposition position are
`(decide (t1 ≤ t) && decide (t ≤ t2)) = true`; the section-local `Let`s (`of_higher_or_equal_priority`,
`of_task_tsk`, `arrivals_between`) are unfolded. Binder lists follow the Rocq contract (definitions take only the
section variables they use).
-/

namespace Prosa.Classic.Model.Schedule.Uni.Workload.Workload

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Util.Sum (sumFiltered)

universe u v

def workload_of_jobs {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (jobs : List Job)
    (P : Job → Bool) : Nat :=
  sumFiltered jobs P job_cost

def workload_of_higher_or_equal_priority_tasks {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (jobs : List Job) (higher_eq_priority : FP_policy Task)
    (tsk : Task) : Nat :=
  workload_of_jobs job_cost jobs (fun j => higher_eq_priority (job_task j) tsk)

def workload_of_higher_or_equal_priority_jobs {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (jobs : List Job) (higher_eq_priority : JLFP_policy Job) (j : Job) : Nat :=
  workload_of_jobs job_cost jobs (fun j_hp => higher_eq_priority j_hp j)

def task_workload {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (tsk : Task) (jobs : List Job) : Nat :=
  workload_of_jobs job_cost jobs (fun j => decide (job_task j = tsk))

def task_workload_between {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task)
    (t1 t2 : time) : Nat :=
  task_workload job_cost job_task tsk (jobs_arrived_between arr_seq t1 t2)

theorem workload_of_jobs_cat {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (arr_seq : arrival_sequence Job) :
    ∀ (t t1 t2 : Nat) (P : Job → Bool),
      (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2) P =
        workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t) P +
          workload_of_jobs job_cost (jobs_arrived_between arr_seq t t2) P := by
  intro t t1 t2 P H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  unfold workload_of_jobs sumFiltered
  rw [job_arrived_between_cat arr_seq t1 t t2 H.1 H.2, List.filter_append, List.map_append, List.sum_append]

end Prosa.Classic.Model.Schedule.Uni.Workload.Workload
