-- Translated from: ../rt-proofs/model/task/sequentiality.v
import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Sequentiality

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Task.Concept

section PropertyOfSequentiality

variable {Job : JobType}
variable {Task : TaskType}
variable [DecidableEq Task]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (sched : schedule PState)

/-- Tasks execute sequentially if each task's jobs are executed in arrival order
    and in a non-overlapping fashion. -/
def sequential_tasks :=
  ∀ (j1 j2 : Job) (t : instant),
    same_task (Task := Task) j1 j2 →
    job_arrival j1 < job_arrival j2 →
    scheduled_at sched j2 t →
    completed_by sched j1 t

end PropertyOfSequentiality

end Prosa.Model.Task.Sequentiality
