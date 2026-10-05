-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/readiness/sequential.v

import Prosa.Behavior.All
import Prosa.Model.Task.Sequentiality

namespace Prosa.Model.Readiness.Sequential

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality

/-- `LEAN_HELPER` for the source's `#[local,program]` instance: in the
sequential readiness model a job is ready iff it is pending and every earlier
job of its task is complete.  The source registers the instance only locally
(and `Task`/`arr_seq` are not inferable), so it is a named definition that
downstream modules select explicitly. -/
@[instance_reducible] noncomputable def sequential_ready_instance {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) : JobReady Job PState where
  job_ready sched j t :=
    pending sched j t && prior_jobs_complete (Task := Task) arr_seq sched j t
  ready_implies_pending sched j t h := by
    revert h
    generalize pending sched j t = b
    cases b
    · exact fun h => h
    · exact fun _ => rfl

end Prosa.Model.Readiness.Sequential
