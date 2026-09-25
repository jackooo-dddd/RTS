-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/absolute_deadline.v

import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.AbsoluteDeadline

open Prosa.Behavior.Job
open Prosa.Model.Task.Concept

universe u v

section
set_option synthInstance.checkSynthOrder false

/-- The absolute deadline is arrival time plus the assigned task's relative
deadline. This is the source's global `JobDeadline` instance. -/
instance job_deadline_from_task_deadline
    (Job : JobType) (Task : TaskType)
    [DecidableEq Job] [DecidableEq Task]
    [TaskDeadline Task] [JobArrival Job] [JobTask Job Task] :
    JobDeadline Job where
  job_deadline j := job_arrival j + task_deadline (job_task (Task := Task) j)

end

end Prosa.Model.Task.AbsoluteDeadline
