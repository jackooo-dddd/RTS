-- Translated from: ../rt-proofs/model/task/absolute_deadline.v
import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Absolute_deadline

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept

/-- Given relative task deadlines and a mapping from jobs to tasks, we provide
    the canonical definition of each job's absolute deadline as the job's
    arrival time plus its task's relative deadline. -/
@[reducible]
noncomputable def job_deadline_from_task_deadline (Job : JobType) (Task : TaskType)
    [TaskDeadline Task] [JobArrival Job] [JobTask Job Task] : JobDeadline Job where
  job_deadline := fun (j : Job) => job_arrival j + task_deadline (job_task (Task := Task) j)

end Prosa.Model.Task.Absolute_deadline
