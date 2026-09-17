-- Translated from: ../rt-proofs/model/task/suspension/dynamic.v
import Prosa.Model.Readiness.Suspension
import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Suspension.Dynamic

open Prosa.Model.Readiness.Suspension
open Prosa.Model.Task.Concept
open Prosa.Behavior.Job
open Prosa.Behavior.Time

/-- Under the dynamic self-suspension model, for each task, there is a bound on
    the maximum total self-suspension duration exhibited by any job of the
    task. -/
class TaskTotalSuspension (Task : TaskType) where
  task_total_suspension : Task → duration

export TaskTotalSuspension (task_total_suspension)

section ValidDynamicSuspensions

variable {Job : JobType}
variable [JobCost Job] [JobSuspension Job]
variable {Task : TaskType}
variable [JobTask Job Task] [TaskTotalSuspension Task]

/-- Under the dynamic self-suspension model, the total self-suspension time
    of any job cannot exceed the self-suspension bound of its associated
    task. -/
def valid_dynamic_suspensions :=
  ∀ j : Job, total_suspension j ≤ task_total_suspension (job_task (Task := Task) j)

end ValidDynamicSuspensions

end Prosa.Model.Task.Suspension.Dynamic
