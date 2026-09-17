-- Translated from: ../rt-proofs/model/task/arrivals.v
import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Arrivals

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept

section TaskArrivals

variable {Job : JobType}
variable {Task : TaskType}
variable [DecidableEq Task]
variable [JobTask Job Task]
variable (arr_seq : arrival_sequence Job)
variable (tsk : Task)

/-- The list of jobs of task `tsk` arriving in the half-open interval `[t1, t2)`. -/
def task_arrivals_between (t1 t2 : instant) : List Job :=
  (arrivals_between arr_seq t1 t2).filter (fun j => job_task j == tsk)

/-- The list of jobs of task `tsk` arriving up to and including time `t`. -/
def task_arrivals_up_to (t : instant) : List Job :=
  task_arrivals_between arr_seq tsk 0 (t + 1)

/-- The list of jobs of task `tsk` arriving strictly before time `t`. -/
def task_arrivals_before (t : instant) : List Job :=
  task_arrivals_between arr_seq tsk 0 t

/-- The number of arrivals of task `tsk` in the interval `[t1, t2)`. -/
def number_of_task_arrivals (t1 t2 : instant) : Nat :=
  (task_arrivals_between arr_seq tsk t1 t2).length

end TaskArrivals

end Prosa.Model.Task.Arrivals
