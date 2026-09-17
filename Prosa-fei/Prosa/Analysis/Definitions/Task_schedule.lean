-- Translated from: ../rt-proofs/analysis/definitions/task_schedule.v
import Prosa.Model.Task.Concept
import Prosa.Model.Processor.Ideal

namespace Prosa.Analysis.Definitions.Task_schedule

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal

section ScheduleOfTask

variable {Task : TaskType}
variable [TaskCost Task]
variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable [DecidableEq Task]

variable (sched : schedule (processor_state Job))
variable (tsk : Task)

/-- Whether a task is scheduled at time t. -/
def task_scheduled_at (t : instant) : Bool :=
  match sched t with
  | some j => job_task j == tsk
  | none => false

/-- The instantaneous service received by a task at time t. -/
def task_service_at (t : instant) : Nat :=
  (task_scheduled_at sched tsk t).toNat

/-- The cumulative service received by a task during [t1, t2). -/
noncomputable def task_service_during (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, task_service_at sched tsk t

/-- The cumulative service received by a task up to time t2, i.e., during [0, t2). -/
noncomputable def task_service (t2 : instant) : Nat :=
  task_service_during sched tsk 0 t2

end ScheduleOfTask

end Prosa.Analysis.Definitions.Task_schedule
