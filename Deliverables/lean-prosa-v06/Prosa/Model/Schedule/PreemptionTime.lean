-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/schedule/preemption_time.v

import Prosa.Model.Schedule.Scheduled
import Prosa.Model.Preemption.Parameter

namespace Prosa.Model.Schedule.PreemptionTime

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Preemption.Parameter

/-! Representation notes: `if o is Some j then a else b` is a `match` on the
`Option`. Binder order follows the elaborated type. -/

/-- `t` is a preemption time if the job scheduled at `t` (if any) is
preemptable at its current progress; an idle instant is a preemption time. -/
noncomputable def preemption_time {Job : JobType} [DecidableEq Job] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (sched : schedule PState) (t : instant) : Bool :=
  match scheduled_job_at arr_seq sched t with
  | some j => job_preemptable j (service sched j t)
  | none => true

end Prosa.Model.Schedule.PreemptionTime
