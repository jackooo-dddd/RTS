-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/aggregate/workload.v

import Prosa.Model.Priority.Classes

namespace Prosa.Model.Aggregate.Workload

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Util.Sum

/-! Representation notes: `\sum_(j <- jobs | P j) job_cost j` is
`sumFiltered jobs P job_cost`; a MathComp `pred Job` is `Job → Bool`;
`predT` is `fun _ => true` and `xpred1 j` is `fun x => decide (x = j)`.
Binder orders follow the elaborated types (the section's unused
`TaskCost`/task context is absent where the definition does not use it). -/

/-- Cumulative cost of the jobs of `jobs` satisfying `P`. -/
def workload_of_jobs {Job : JobType} [DecidableEq Job] [JobCost Job]
    (P : Job → Bool) (jobs : List Job) : Nat :=
  sumFiltered jobs P (fun j => job_cost j)

/-- Workload of the jobs of task `tsk` in `jobs`. -/
def task_workload {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] (tsk : Task) (jobs : List Job) : Nat :=
  workload_of_jobs (job_of_task tsk) jobs

/-- Workload of the jobs of task `tsk` arriving in `[t1, t2)`. -/
def task_workload_between {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [JobTask Job Task] [JobCost Job] (arr_seq : arrival_sequence Job)
    (tsk : Task) (t1 t2 : instant) : Nat :=
  task_workload tsk (arrivals_between arr_seq t1 t2)

/-- Workload of job `j` among the arrivals in `[t1, t2)`. -/
def workload_of_job {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (j : Job) (t1 t2 : instant) : Nat :=
  workload_of_jobs (fun x => decide (x = j)) (arrivals_between arr_seq t1 t2)

/-- Total workload of `jobs`. -/
def total_workload {Job : JobType} [DecidableEq Job] [JobCost Job] (jobs : List Job) : Nat :=
  workload_of_jobs (fun _ => true) jobs

/-- Total workload of the arrivals in `[t1, t2)`. -/
def total_workload_between {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) (t1 t2 : instant) : Nat :=
  total_workload (arrivals_between arr_seq t1 t2)

/-- Workload of the higher-or-equal-priority jobs arriving in `[t1, t2)`. -/
def workload_of_hep_jobs {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) [JLFP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  let is_hep := fun j' => hep_job j' j
  workload_of_jobs is_hep (arrivals_between arr_seq t1 t2)

/-- Workload of the other higher-or-equal-priority jobs arriving in `[t1, t2)`. -/
def workload_of_other_hep_jobs {Job : JobType} [DecidableEq Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) [JLFP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  let is_ahep := fun j' => another_hep_job j' j
  workload_of_jobs is_ahep (arrivals_between arr_seq t1 t2)

end Prosa.Model.Aggregate.Workload
