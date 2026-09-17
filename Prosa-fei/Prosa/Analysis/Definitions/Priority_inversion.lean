-- Translated from: ../rt-proofs/analysis/definitions/priority_inversion.v
import Prosa.Analysis.Definitions.Busy_interval

namespace Prosa.Analysis.Definitions.Priority_inversion

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Classes
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Definitions.Busy_interval

section CumulativePriorityInversion

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

variable [JLFP_policy Job]

section JobPriorityInversionBound

variable (tsk : Task)
variable (j : Job)
variable (H_from_arrival_sequence : arrives_in arr_seq j)
variable (H_job_task : job_task j = tsk)

noncomputable def is_priority_inversion (t : instant) : Bool :=
  match sched t with
  | some jlp => !hep_job jlp j
  | none => false

noncomputable def cumulative_priority_inversion (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (is_priority_inversion sched j t).toNat

def priority_inversion_of_job_is_bounded_by (B : duration) : Prop :=
  ∀ (t1 t2 : instant),
    busy_interval_prefix arr_seq sched j t1 t2 →
    cumulative_priority_inversion sched j t1 t2 ≤ B

end JobPriorityInversionBound

section TaskPriorityInversionBound

variable (tsk : Task)

def priority_inversion_is_bounded_by (B : duration) : Prop :=
  ∀ (j : Job),
    arrives_in arr_seq j →
    job_task j = tsk →
    job_cost j > 0 →
    priority_inversion_of_job_is_bounded_by arr_seq sched j B

end TaskPriorityInversionBound

end CumulativePriorityInversion

end Prosa.Analysis.Definitions.Priority_inversion
