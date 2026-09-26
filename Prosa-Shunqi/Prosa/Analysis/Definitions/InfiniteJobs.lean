-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/infinite_jobs.v

import Prosa.Model.Task.Arrivals

namespace Prosa.Analysis.Definitions.InfiniteJobs

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals

section InfiniteJobs

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job]
variable [JobTask Job Task] [JobArrival Job]
variable (arr_seq : arrival_sequence Job)

/-- Every task releases a job with every index `n`. -/
def infinite_jobs : Prop :=
  ∀ (tsk : Task) (n : Nat), ∃ j : Job,
    arrives_in arr_seq j ∧ job_task j = tsk ∧ job_index (Task := Task) arr_seq j = n

end InfiniteJobs

end Prosa.Analysis.Definitions.InfiniteJobs
