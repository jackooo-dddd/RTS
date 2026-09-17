-- Translated from: ../rt-proofs/analysis/definitions/carry_in.v
import Prosa.Model.Priority.Classes
import Prosa.Model.Processor.Ideal

namespace Prosa.Analysis.Definitions.Carry_in

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Model.Task.Concept
open Prosa.Model.Processor.Ideal

section NoCarryIn

variable {Task : TaskType}
variable [TaskCost Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)

variable (sched : schedule (processor_state Job))

/-- The processor has no carry-in at time t iff every job from the arrival sequence
    released before t has completed by that time. -/
def no_carry_in (t : instant) :=
  ∀ j_o,
    arrives_in arr_seq j_o →
    arrived_before j_o t →
    completed_by sched j_o t

end NoCarryIn

end Prosa.Analysis.Definitions.Carry_in
