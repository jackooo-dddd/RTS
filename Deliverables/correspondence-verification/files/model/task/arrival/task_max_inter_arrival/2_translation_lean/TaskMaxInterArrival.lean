-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrival/task_max_inter_arrival.v

import Prosa.Model.Task.Concept
import Prosa.Model.Task.Arrivals

namespace Prosa.Model.Task.Arrival.Task_max_inter_arrival

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals

/-- The maximum time difference between the arrivals of consecutive jobs. -/
class TaskMaxInterArrival (Task : TaskType) [DecidableEq Task] where
  task_max_inter_arrival_time : Task → duration

export TaskMaxInterArrival (task_max_inter_arrival_time)

/-- The maximum inter-arrival time of `tsk` is positive. -/
def positive_task_max_inter_arrival_time {Task : TaskType} [DecidableEq Task]
    [TaskMaxInterArrival Task] (tsk : Task) : Bool :=
  decide (0 < task_max_inter_arrival_time tsk)

/-- Every job of `tsk` with a positive index has an earlier job of `tsk` that
arrived at most `task_max_inter_arrival_time tsk` before it. -/
def arr_sep_task_max_inter_arrival {Task : TaskType} [DecidableEq Task]
    [TaskMaxInterArrival Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (tsk : Task) : Prop :=
  ∀ j : Job,
    arrives_in arr_seq j →
    job_task j = tsk →
    0 < job_index (Task := Task) arr_seq j →
    ∃ j' : Job,
      j ≠ j' ∧
      arrives_in arr_seq j' ∧
      job_task j' = tsk ∧
      (decide (job_arrival j' ≤ job_arrival j) &&
        decide (job_arrival j ≤ job_arrival j' + task_max_inter_arrival_time tsk)) = true

/-- The maximum inter-arrival time of `tsk` is valid. -/
def valid_task_max_inter_arrival_time {Task : TaskType} [DecidableEq Task]
    [TaskMaxInterArrival Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (tsk : Task) : Prop :=
  positive_task_max_inter_arrival_time tsk = true ∧ arr_sep_task_max_inter_arrival arr_seq tsk

/-- Every task of the task set has a valid maximum inter-arrival time. -/
def taskset_respects_task_max_inter_arrival_model {Task : TaskType} [DecidableEq Task]
    [TaskMaxInterArrival Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (ts : TaskSet Task) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_task_max_inter_arrival_time arr_seq tsk

end Prosa.Model.Task.Arrival.Task_max_inter_arrival
