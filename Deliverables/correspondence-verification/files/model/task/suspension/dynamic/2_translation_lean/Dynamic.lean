-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/suspension/dynamic.v

import Prosa.Model.Readiness.Suspension
import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Suspension.Dynamic

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Readiness.Suspension

/-! Task parameter and validity of the dynamic self-suspension model.

Representation: `a <= b` in `Prop` position is `a ≤ b`. -/

/-- Under the dynamic self-suspension model, each task bounds the total self-suspension of any of its jobs. -/
class TaskTotalSuspension (Task : TaskType) [DecidableEq Task] where
  task_total_suspension : Task → duration

export TaskTotalSuspension (task_total_suspension)

section ValidDynamicSuspensions

variable {Job : JobType} [DecidableEq Job]
variable [JobCost Job] [JobSuspension Job]
variable {Task : TaskType} [DecidableEq Task]
variable [JobTask Job Task] [TaskTotalSuspension Task]

/-- The total self-suspension of every job is at most the bound of its task. -/
def valid_dynamic_suspensions : Prop :=
  ∀ j : Job, total_suspension j ≤ task_total_suspension (job_task (Task := Task) j)

end ValidDynamicSuspensions

end Prosa.Model.Task.Suspension.Dynamic
