-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/service.v

import Prosa.Behavior.Service

namespace Prosa.Analysis.Definitions.Service

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u v w

section ServedAt

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

/-- Jobs arriving by `t` that receive positive service at `t`, preserving
the source sequence order and multiplicity. -/
noncomputable def served_jobs_at (t : instant) : List Job :=
  (arrivals_up_to arr_seq t).filter (fun j => receives_service_at sched j t)

/-- The optional first job receiving service at `t`. -/
noncomputable def served_job_at (t : instant) : Option Job :=
  (served_jobs_at arr_seq sched t).head?

end ServedAt

end Prosa.Analysis.Definitions.Service
