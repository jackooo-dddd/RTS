-- Translated from: ../rt-proofs/model/schedule/preemption_time.v
import Prosa.Model.Preemption.Parameter
import Prosa.Model.Processor.Ideal

namespace Prosa.Model.Schedule.Preemption_time

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Processor.Ideal

section PreemptionTime

variable {Job : JobType} [DecidableEq Job]
variable [JobPreemptable Job]
variable (sched : schedule (processor_state Job))

/-- A time `t` is a preemption time iff the job currently scheduled at `t`, if any,
    can be preempted according to `job_preemptable`. An idle instant is always a
    preemption time. -/
noncomputable def preemption_time (t : instant) : Bool :=
  match sched t with
  | some j => job_preemptable j (service sched j t)
  | none => true

end PreemptionTime

end Prosa.Model.Schedule.Preemption_time
