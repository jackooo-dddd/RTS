-- Translated from: ../rt-proofs/model/task/arrival/sporadic.v
import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Arrival.Sporadic

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept

/-- Under the sporadic task model, each task is characterized by its minimum
    inter-arrival time. -/
class SporadicModel (Task : TaskType) where
  task_min_inter_arrival_time : Task → duration

export SporadicModel (task_min_inter_arrival_time)

section ValidSporadicTaskModel

variable {Task : TaskType} [SporadicModel Task]

/-- A valid sporadic task should have a non-zero minimum inter-arrival time. -/
def valid_task_min_inter_arrival_time (tsk : Task) :=
  task_min_inter_arrival_time tsk > 0

variable (ts : TaskSet Task)

/-- Every task in the set should have a valid inter-arrival time. -/
def valid_taskset_inter_arrival_times :=
  ∀ tsk : Task, tsk ∈ ts → valid_task_min_inter_arrival_time tsk

variable {Job : JobType} [JobTask Job Task] [JobArrival Job]
variable (arr_seq : arrival_sequence Job)

/-- A task respects the sporadic task model if the arrivals of its jobs
    are appropriately spaced in time. -/
def respects_sporadic_task_model (tsk : Task) :=
  ∀ (j j' : Job),
    j ≠ j' →
    arrives_in arr_seq j →
    arrives_in arr_seq j' →
    job_task j = tsk →
    job_task j' = tsk →
    job_arrival j ≤ job_arrival j' →
    job_arrival j' ≥ job_arrival j + task_min_inter_arrival_time tsk

/-- The sporadic task model requires every task in the set to respect the
    sporadic arrival constraint. -/
def taskset_respects_sporadic_task_model :=
  ∀ tsk, tsk ∈ ts → respects_sporadic_task_model arr_seq tsk

end ValidSporadicTaskModel

end Prosa.Model.Task.Arrival.Sporadic
