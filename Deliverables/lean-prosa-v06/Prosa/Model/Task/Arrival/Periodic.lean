-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrival/periodic.v

import Prosa.Model.Task.Arrivals

namespace Prosa.Model.Task.Arrival.Periodic

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals

/-! Representation notes: `a > b` in a Boolean position is `decide (b < a)`;
a single comparison in `Prop` position is the Lean proposition; `x \in s` is
`decide (x ∈ s) = true`; `TaskSet Task` is the accepted `List Task`. Binder
orders follow the elaborated types. -/

/-- The periodic task model: each task has a period. -/
class PeriodicModel (Task : TaskType) [DecidableEq Task] where
  task_period : Task → duration

export PeriodicModel (task_period)

section ValidPeriodicTaskModel

variable {Task : TaskType} [DecidableEq Task] [PeriodicModel Task]

/-- A valid period is positive. -/
def valid_period (tsk : Task) : Bool := decide (0 < task_period tsk)

variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
variable (arr_seq : arrival_sequence Job)

/-- Every job of `tsk` other than the first has a predecessor released one
period earlier. -/
def respects_periodic_task_model (tsk : Task) : Prop :=
  ∀ j : Job, arrives_in arr_seq j → 0 < job_index (Task := Task) arr_seq j → job_task j = tsk →
    ∃ j' : Job, arrives_in arr_seq j' ∧
      job_index (Task := Task) arr_seq j' = job_index (Task := Task) arr_seq j - 1 ∧
      job_task j' = tsk ∧ job_arrival j = job_arrival j' + task_period tsk

end ValidPeriodicTaskModel

section TaskSet

variable {Task : TaskType} [DecidableEq Task] [PeriodicModel Task]

/-- Every task of the task set has a valid period. -/
def valid_periods (ts : TaskSet Task) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_period tsk = true

variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]

/-- Every task of the task set respects the periodic model. -/
def taskset_respects_periodic_task_model (arr_seq : arrival_sequence Job) (ts : TaskSet Task) : Prop :=
  ∀ tsk, decide (tsk ∈ ts) = true → respects_periodic_task_model arr_seq tsk

end TaskSet

end Prosa.Model.Task.Arrival.Periodic
