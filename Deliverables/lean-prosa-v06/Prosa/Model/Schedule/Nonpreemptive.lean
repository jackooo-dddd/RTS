-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/schedule/nonpreemptive.v

import Prosa.Behavior.All

namespace Prosa.Model.Schedule.Nonpreemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time

universe u

/-- A job running at time `t` keeps running at every later instant until it
has completed. This is the v0.6 Boolean-observation contract. -/
noncomputable def nonpreemptive_schedule {Job : JobType}
    [DecidableEq Job] [JobCost Job]
    {PState : ProcessorState Job} (sched : schedule PState) : Prop :=
  ∀ (j : Job) (t t' : instant),
    t ≤ t' →
    scheduled_at sched j t = true →
    (!completed_by sched j t') = true →
    scheduled_at sched j t' = true

end Prosa.Model.Schedule.Nonpreemptive
