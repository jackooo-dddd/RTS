-- Translated from: ../rt-proofs/model/schedule/nonpreemptive.v
import Prosa.Behavior.All

namespace Prosa.Model.Schedule.Nonpreemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service

section NonpreemptiveSchedule

variable {Job : JobType}
variable [JobCost Job]
variable {PState : Type _}
variable [ProcessorState Job PState]

def nonpreemptive_schedule (sched : schedule PState) : Prop :=
  ∀ (j : Job) (t t' : instant),
    t ≤ t' →
    scheduled_at sched j t = true →
    ¬ completed_by sched j t' →
    scheduled_at sched j t' = true

end NonpreemptiveSchedule

end Prosa.Model.Schedule.Nonpreemptive
