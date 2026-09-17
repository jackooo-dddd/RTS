-- Translated from: ../rt-proofs/model/preemption/limited_preemptive.v
import Prosa.Model.Preemption.Parameter
import Prosa.Util.Nondecreasing

namespace Prosa.Model.Preemption.Limited_preemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Preemption.Parameter
open Prosa.Util.List
open Prosa.Util.Nondecreasing

class JobPreemptionPoints (Job : JobType) where
  job_preemption_points : Job → List work

export JobPreemptionPoints (job_preemption_points)

section LimitedPreemptions

variable {Job : JobType}
variable [JobArrival Job]
variable [JobCost Job]
variable [JobPreemptionPoints Job]

instance limited_preemptions_model : JobPreemptable Job where
  job_preemptable (j : Job) (ρ : work) := decide (ρ ∈ job_preemption_points j)

section ValidLimitedPreemptiveModel

variable (arr_seq : arrival_sequence Job)

def beginning_of_execution_in_preemption_points :=
  ∀ j, arrives_in arr_seq j → 0 ∈ job_preemption_points j

def end_of_execution_in_preemption_points :=
  ∀ j, arrives_in arr_seq j → last0 (job_preemption_points j) = job_cost j

def preemption_points_is_nondecreasing_sequence :=
  ∀ j, arrives_in arr_seq j → nondecreasing_sequence (job_preemption_points j)

def valid_limited_preemptions_job_model :=
  beginning_of_execution_in_preemption_points arr_seq ∧
  end_of_execution_in_preemption_points arr_seq ∧
  preemption_points_is_nondecreasing_sequence arr_seq

end ValidLimitedPreemptiveModel

end LimitedPreemptions

end Prosa.Model.Preemption.Limited_preemptive
