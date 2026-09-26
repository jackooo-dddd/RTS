-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/jitter.v

import Prosa.Model.Task.Concept
import Prosa.Model.Readiness.Jitter

namespace Prosa.Model.Task.Jitter

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Readiness.Jitter

/-- A bound on the release jitter experienced by any job of a task. -/
class TaskJitter (Task : TaskType) [DecidableEq Task] where
  task_jitter : Task → duration

export TaskJitter (task_jitter)

section ValidTaskJitter

variable {Task : TaskType} [DecidableEq Task] [TaskJitter Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobJitter Job]

/-- The task's jitter bound upper-bounds the jitter of each of its jobs. -/
def valid_jitter (tsk : Task) : Prop :=
  ∀ j : Job, job_task j = tsk → job_jitter j ≤ task_jitter tsk

/-- Every task in the task set has a valid jitter bound. -/
def valid_jitter_bounds (ts : TaskSet Task) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_jitter (Job := Job) tsk

end ValidTaskJitter

end Prosa.Model.Task.Jitter
