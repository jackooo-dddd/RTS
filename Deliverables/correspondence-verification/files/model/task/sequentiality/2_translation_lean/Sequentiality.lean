-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/sequentiality.v

import Prosa.Model.Task.Concept
import Prosa.Model.Task.Arrivals

namespace Prosa.Model.Task.Sequentiality

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals

/-- Each task's jobs execute in arrival order and do not overlap. -/
def sequential_tasks {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) : Prop :=
  ∀ (j1 j2 : Job) (t : instant),
    arrives_in arr_seq j1 →
    arrives_in arr_seq j2 →
    same_task (Task := Task) j1 j2 = true →
    job_arrival j1 < job_arrival j2 →
    scheduled_at sched j2 t = true →
    completed_by sched j1 t = true

/-- Every job of `j`'s task that arrived before `j` is completed by `t`. -/
noncomputable def prior_jobs_complete {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (j : Job) (t : instant) : Bool :=
  (task_arrivals_before arr_seq (job_task (Task := Task) j) (job_arrival j)).all
    (fun j_tsk => completed_by sched j_tsk t)

end Prosa.Model.Task.Sequentiality
