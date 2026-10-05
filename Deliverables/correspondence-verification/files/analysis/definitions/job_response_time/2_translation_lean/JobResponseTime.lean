-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/job_response_time.v

import Prosa.Behavior.All

namespace Prosa.Analysis.Definitions.JobResponseTime

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u

section

variable {Job : JobType} [DecidableEq Job]
variable [JobCost Job] [JobArrival Job]
variable {PState : ProcessorState Job}
variable (sched : schedule PState)

/-- A job's response time exceeds `x` exactly when it has not completed at
its arrival time plus `x`. -/
noncomputable def job_response_time_exceeds (j : Job) (x : duration) : Bool :=
  !completed_by sched j (job_arrival j + x)

end

end Prosa.Analysis.Definitions.JobResponseTime
