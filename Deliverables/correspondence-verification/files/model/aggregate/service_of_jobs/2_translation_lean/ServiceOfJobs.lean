-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/aggregate/service_of_jobs.v

import Prosa.Model.Priority.Classes

namespace Prosa.Model.Aggregate.ServiceOfJobs

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Util.Sum

/-! Representation notes: `\sum_(j <- jobs | P j) F j` is
`sumFiltered jobs P F`; a MathComp `pred Job` is `Job → Bool`; `predT` is
`fun _ => true`. Binder orders follow the elaborated types (the section's
unused task context is absent where the source definition does not use it). -/

/-- Cumulative service received at `t` by the jobs of `jobs` satisfying `P`. -/
noncomputable def service_of_jobs_at {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (P : Job → Bool)
    (jobs : List Job) (t : instant) : Nat :=
  sumFiltered jobs P (fun j => service_at sched j t)

/-- Cumulative service received during `[t1, t2)` by the jobs satisfying `P`. -/
noncomputable def service_of_jobs {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (P : Job → Bool)
    (jobs : List Job) (t1 t2 : instant) : Nat :=
  sumFiltered jobs P (fun j => service_during sched j t1 t2)

/-- Service of the jobs of `jobs` with higher-or-equal priority than `j`. -/
noncomputable def service_of_higher_or_equal_priority_jobs {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) [JLFP_policy Job]
    (jobs : List Job) (j : Job) (t1 t2 : instant) : Nat :=
  service_of_jobs sched (fun j_hp => hep_job j_hp j) jobs t1 t2

/-- Service of the other higher-or-equal-priority jobs arriving in `[t1, t2)`. -/
noncomputable def service_of_other_hep_jobs {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLFP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  service_of_jobs sched (fun jhp => another_hep_job jhp j) (arrivals_between arr_seq t1 t2) t1 t2

/-- Service of higher-or-equal-priority jobs of other tasks arriving in `[t1, t2)`. -/
noncomputable def service_of_other_task_hep_jobs {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) [JLFP_policy Job]
    (j : Job) (t1 t2 : instant) : Nat :=
  service_of_jobs sched (fun jhp => another_task_hep_job (Task := Task) jhp j)
    (arrivals_between arr_seq t1 t2) t1 t2

/-- Service of the higher-or-equal-priority jobs arriving in `[t1, t2)`. -/
noncomputable def service_of_hep_jobs {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)
    [JLFP_policy Job] (j : Job) (t1 t2 : instant) : Nat :=
  service_of_jobs sched (fun jhp => hep_job jhp j) (arrivals_between arr_seq t1 t2) t1 t2

/-- Service received during `[t1, t2)` by the jobs of task `tsk` in `jobs`. -/
noncomputable def task_service_of_jobs_in {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] {PState : ProcessorState Job}
    (sched : schedule PState) (tsk : Task) (jobs : List Job) (t1 t2 : instant) : Nat :=
  service_of_jobs sched (job_of_task tsk) jobs t1 t2

/-- Total service received during `[t1, t2)` by all jobs of `jobs`. -/
noncomputable def total_service_of_jobs_in {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState) (jobs : List Job)
    (t1 t2 : instant) : Nat :=
  service_of_jobs sched (fun _ => true) jobs t1 t2

end Prosa.Model.Aggregate.ServiceOfJobs
