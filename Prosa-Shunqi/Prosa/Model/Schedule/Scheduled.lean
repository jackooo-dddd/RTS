-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/schedule/scheduled.v

import Prosa.Behavior.All
import Prosa.Util.Epsilon

namespace Prosa.Model.Schedule.Scheduled

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u v w

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}

/-- Jobs that arrived by `t` and are scheduled at `t`, preserving arrival
sequence order and multiplicity. -/
def scheduled_jobs_at (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (t : instant) : List Job :=
  (arrivals_up_to arr_seq t).filter fun j => scheduled_at sched j t

/-- First scheduled job, if any. -/
def scheduled_job_at (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (t : instant) : Option Job :=
  (scheduled_jobs_at arr_seq sched t).head?

/-- Boolean absence of scheduled jobs. -/
def is_idle (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (t : instant) : Bool :=
  (scheduled_jobs_at arr_seq sched t).isEmpty

end Prosa.Model.Schedule.Scheduled
