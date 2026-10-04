-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/schedule/edf.v

import Prosa.Behavior.All

namespace Prosa.Model.Schedule.Edf

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u v w

variable {Job : JobType} [DecidableEq Job]
variable [JobDeadline Job] [JobArrival Job]
variable {PState : ProcessorState Job}

/-- A schedule is locally EDF-compliant at `t` if each job scheduled at `t`
has a deadline no later than any job that had already arrived at `t` but is
scheduled at `t` or later.  As in the source, this does not assert work
conservation, readiness, or a preemption model. -/
def EDF_at (sched : schedule PState) (t : instant) : Prop :=
  ∀ (j : Job), scheduled_at sched j t = true →
    ∀ (t' : instant) (j' : Job),
      t ≤ t' →
      scheduled_at sched j' t' = true →
      job_arrival j' ≤ t →
      job_deadline j ≤ job_deadline j'

/-- A schedule is EDF-compliant when it is locally compliant at every time. -/
def EDF_schedule (sched : schedule PState) : Prop :=
  ∀ t : instant, EDF_at sched t

end Prosa.Model.Schedule.Edf
