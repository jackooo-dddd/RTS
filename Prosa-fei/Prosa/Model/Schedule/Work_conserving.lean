-- Translated from: ../rt-proofs/model/schedule/work_conserving.v
import Prosa.Behavior.All

namespace Prosa.Model.Schedule.Work_conserving

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready

section WorkConserving

variable {Job : JobType}
variable [JobArrival Job]
variable [JobCost Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable [JobReady Job PState]

variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

def work_conserving :=
  ∀ j t,
    arrives_in arr_seq j →
    backlogged sched j t = true →
    ∃ j_other : Job, scheduled_at sched j_other t = true

end WorkConserving

end Prosa.Model.Schedule.Work_conserving
