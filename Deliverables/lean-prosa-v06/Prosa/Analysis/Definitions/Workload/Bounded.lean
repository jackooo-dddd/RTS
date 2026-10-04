-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/workload/bounded.v

import Prosa.Model.Aggregate.Workload
import Prosa.Model.Job.Properties
import Prosa.Analysis.Definitions.BusyInterval.Classical

namespace Prosa.Analysis.Definitions.Workload.Bounded

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Job.Properties
open Prosa.Model.Priority.Definitions
open Prosa.Model.Aggregate.Workload
open Prosa.Analysis.Definitions.BusyInterval.Classical

/-! Representation notes: a Boolean in `Prop` position is `= true`; a single
comparison in `Prop` position is the Lean proposition; `f^~ y` is
`fun x => f x y`. Binder orders follow the elaborated types (the JLFP policy
precedes `arr_seq` as in the source context). -/

section WorkloadBound

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job] [JobTask Job Task]
variable {PState : ProcessorState Job}
variable [JLFP : JLFP_policy Job]
variable (arr_seq : arrival_sequence Job) (sched : schedule PState) (tsk : Task)

/-- `B` bounds the higher-or-equal-priority workload of tasks other than
`tsk` in any interval starting with a quiet time. -/
def athep_workload_is_bounded (B : duration → duration → work) : Prop :=
  ∀ (j : Job) (t1 : instant) (Δ : duration),
    job_cost_positive j = true →
    job_of_task tsk j = true →
    quiet_time arr_seq sched j t1 →
    workload_of_jobs (fun j' => another_task_hep_job (Task := Task) j' j) (arrivals_between arr_seq t1 (t1 + Δ))
      ≤ B (job_arrival j - t1) Δ

end WorkloadBound

end Prosa.Analysis.Definitions.Workload.Bounded
