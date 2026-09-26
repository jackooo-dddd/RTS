-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/schedule/limited_preemptive.v

import Prosa.Model.Preemption.Parameter

namespace Prosa.Model.Schedule.LimitedPreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Preemption.Parameter

/-! Representation notes: `~~ b` is `!b` and a Boolean in `Prop` position is
`= true`. Binder order follows the elaborated type. -/

/-- A schedule respects the preemption model: an arriving job that is not
preemptable at its current progress is scheduled. -/
def schedule_respects_preemption_model {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (sched : schedule PState) : Prop :=
  ∀ j t, arrives_in arr_seq j →
    (!job_preemptable j (service sched j t)) = true →
    scheduled_at sched j t = true

end Prosa.Model.Schedule.LimitedPreemptive
