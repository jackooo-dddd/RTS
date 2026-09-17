-- Translated from: ../rt-proofs/analysis/definitions/request_bound_function.v
import Prosa.Model.Task.Arrival.Curves
import Prosa.Model.Priority.Classes
import Prosa.Analysis.Facts.Model.Ideal_schedule

namespace Prosa.Analysis.Definitions.Request_bound_function

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Priority.Classes
open Prosa.Model.Processor.Ideal

section TaskWorkloadBoundedByArrivalCurves

variable {Task : TaskType}
variable [TaskCost Task]

variable {Job : JobType}
variable [JobTask Job Task]
variable [JobCost Job]

variable (sched : schedule (processor_state Job))

variable [FP_policy Task]

variable [MaxArrivals Task]

section SingleTask

variable (tsk : Task)
variable (delta : duration)

def task_request_bound_function :=
  task_cost tsk * max_arrivals tsk delta

end SingleTask

section AllTasks

variable (ts : List Task)
variable (tsk : Task)
variable (delta : duration)

def total_request_bound_function :=
  (ts.map (fun tsk' => task_request_bound_function tsk' delta)).sum

def total_hep_request_bound_function_FP :=
  ((ts.filter (fun tsk_other => hep_task tsk_other tsk)).map
    (fun tsk_other => task_request_bound_function tsk_other delta)).sum

def total_ohep_request_bound_function_FP [DecidableEq Task] :=
  ((ts.filter (fun tsk_other => hep_task tsk_other tsk && decide (tsk_other ≠ tsk))).map
    (fun tsk_other => task_request_bound_function tsk_other delta)).sum

end AllTasks

end TaskWorkloadBoundedByArrivalCurves

end Prosa.Analysis.Definitions.Request_bound_function
