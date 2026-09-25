-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrival/sporadic.v

import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Arrival.Sporadic

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept

universe u v

/-- Minimum duration between the arrivals of two jobs of the same task. -/
class SporadicModel (Task : TaskType) [DecidableEq Task] where
  task_min_inter_arrival_time : Task → duration

export SporadicModel (task_min_inter_arrival_time)

section ValidSporadicTaskModel

variable {Task : TaskType} [DecidableEq Task] [SporadicModel Task]

/-- The minimum inter-arrival time of a task is positive. -/
def valid_task_min_inter_arrival_time (tsk : Task) : Bool :=
  decide (0 < task_min_inter_arrival_time tsk)

variable (ts : TaskSet Task)

/-- Every task in the task set has a positive minimum inter-arrival time. -/
def valid_taskset_inter_arrival_times : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true →
    valid_task_min_inter_arrival_time tsk = true

variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
variable (arr_seq : arrival_sequence Job)

/-- Arrivals of distinct jobs of a given task respect its minimum spacing. -/
def respects_sporadic_task_model (tsk : Task) : Prop :=
  ∀ j j' : Job,
    j ≠ j' →
    arrives_in arr_seq j →
    arrives_in arr_seq j' →
    job_task j = tsk →
    job_task j' = tsk →
    job_arrival j ≤ job_arrival j' →
    job_arrival j + task_min_inter_arrival_time tsk ≤ job_arrival j'

/-- Every task in the task set obeys the sporadic arrival model. -/
def taskset_respects_sporadic_task_model : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true →
    respects_sporadic_task_model arr_seq tsk

end ValidSporadicTaskModel

end Prosa.Model.Task.Arrival.Sporadic
