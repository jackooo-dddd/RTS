-- Translated from: ../rt-proofs/model/schedule/limited_preemptive.v
import Prosa.Model.Preemption.Parameter

namespace Prosa.Model.Schedule.Limited_preemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Preemption.Parameter

section ScheduleWithLimitedPreemptions

variable {Job : JobType}
variable {PState : Type _} [ProcessorState Job PState]
variable [JobPreemptable Job]
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

def schedule_respects_preemption_model :=
  ∀ j t,
    arrives_in arr_seq j →
    ¬(job_preemptable j (service sched j t) = true) →
    scheduled_at sched j t = true

end ScheduleWithLimitedPreemptions

end Prosa.Model.Schedule.Limited_preemptive
