-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/tardiness.v

import Prosa.Analysis.Definitions.Schedulability

namespace Prosa.Analysis.Definitions.Tardiness

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Analysis.Definitions.Schedulability

/-! Representation notes: the definition rebinds `arr_seq sched tsk B`
explicitly, so the unused section variables are absent. Binder orders follow
the elaborated types. -/

section Tardiness

variable {Task : TaskType} [DecidableEq Task] [TaskDeadline Task]
variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job] [JobTask Job Task]
variable {PState : ProcessorState Job}

/-- `B` bounds the tardiness of `tsk`: every job of `tsk` completes within
`B` time units after its deadline. -/
def task_tardiness_is_bounded (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (tsk : Task) (B : duration) : Prop :=
  task_response_time_bound arr_seq sched tsk (task_deadline tsk + B)

end Tardiness

end Prosa.Analysis.Definitions.Tardiness
