-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/offset.v

import Prosa.Behavior.All
import Prosa.Model.Task.Concept
import Prosa.Model.Task.Arrivals
import Prosa.Util.List

namespace Prosa.Model.Task.Offset

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Util.List

/-! Representation notes: a single comparison in `Prop` position is the Lean
proposition (`a >= b` is `b ≤ a`); `x \in s` is `decide (x ∈ s) = true`;
`map f s` is `s.map f`; `TaskSet Task` is the accepted `List Task`. Binder
orders follow the elaborated types (the unused `arr_seq` is absent from
`no_jobs_before_offset`). -/

/-- Each task has an offset: the instant its first job arrives. -/
class TaskOffset (Task : TaskType) [DecidableEq Task] where
  task_offset : Task → instant

export TaskOffset (task_offset)

section ValidTaskOffset

variable {Task : TaskType} [DecidableEq Task] [TaskOffset Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]

/-- No job of `tsk` arrives before its offset. -/
def no_jobs_before_offset (tsk : Task) : Prop :=
  ∀ j : Job, job_task j = tsk → task_offset tsk ≤ job_arrival j

variable (arr_seq : arrival_sequence Job)

/-- Some job of `tsk` arrives exactly at its offset. -/
def job_released_at_offset (tsk : Task) : Prop :=
  ∃ j' : Job, arrives_in arr_seq j' ∧ job_task j' = tsk ∧ job_arrival j' = task_offset tsk

/-- A valid offset satisfies both properties. -/
def valid_offset (tsk : Task) : Prop :=
  no_jobs_before_offset (Job := Job) tsk ∧ job_released_at_offset arr_seq tsk

/-- Every task of the task set has a valid offset. -/
def valid_offsets (ts : TaskSet Task) : Prop :=
  ∀ tsk, decide (tsk ∈ ts) = true → valid_offset arr_seq tsk

end ValidTaskOffset

section MaxTaskOffset

variable {Task : TaskType} [DecidableEq Task] [TaskOffset Task]

/-- The offsets of the tasks of a task set. -/
def task_offsets (ts : TaskSet Task) : List instant := ts.map task_offset

/-- The largest offset of a task set. -/
def max_task_offset (ts : TaskSet Task) : Nat := max0 (task_offsets ts)

end MaxTaskOffset

end Prosa.Model.Task.Offset
