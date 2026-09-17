-- Translated from: ../rt-proofs/model/preemption/parameter.v
import Prosa.Util.List
import Prosa.Util.Epsilon
import Prosa.Behavior.All

namespace Prosa.Model.Preemption.Parameter

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Service
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Util.List
open Prosa.Util.Epsilon

class JobPreemptable (Job : JobType) where
  job_preemptable : Job → work → Bool

export JobPreemptable (job_preemptable)

section MaxAndLastNonpreemptiveSegment

variable {Job : JobType}
variable [JobArrival Job]
variable [JobCost Job]
variable [JobPreemptable Job]

def distances (xs : List ℕ) : List ℕ :=
  (xs.zip (xs.drop 1)).map (fun p => p.2 - p.1)

def job_preemption_points (j : Job) : List work :=
  (range 0 (job_cost j)).filter (fun ρ => job_preemptable j ρ)

theorem conversion_preserves_equivalence :
    ∀ (j : Job) (ρ : work),
      ρ ≤ job_cost j →
      (job_preemptable j ρ = true ↔ ρ ∈ job_preemption_points j) := by
  intro j ρ hle
  unfold job_preemption_points range
  rw [List.mem_filter]
  constructor
  · intro hp
    refine ⟨?_, hp⟩
    rw [List.mem_range']
    refine ⟨ρ, ?_, ?_⟩
    · unfold work at *; omega
    · unfold work at *; omega
  · intro ⟨_, hp⟩
    exact hp

def lengths_of_segments (j : Job) : List ℕ := distances (job_preemption_points j)

def job_max_nonpreemptive_segment (j : Job) : ℕ := max0 (lengths_of_segments j)

def job_last_nonpreemptive_segment (j : Job) : ℕ := last0 (lengths_of_segments j)

def job_run_to_completion_threshold (j : Job) : ℕ :=
  job_cost j - (job_last_nonpreemptive_segment j - ε)

end MaxAndLastNonpreemptiveSegment

section PreemptionModel

variable {Job : JobType}
variable [JobArrival Job]
variable [JobCost Job]
variable [JobPreemptable Job]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

def job_cannot_become_nonpreemptive_before_execution (j : Job) : Prop :=
  job_preemptable j 0 = true

def job_cannot_be_nonpreemptive_after_completion (j : Job) : Prop :=
  job_preemptable j (job_cost j) = true

def not_preemptive_implies_scheduled (j : Job) : Prop :=
  ∀ t,
    ¬(job_preemptable j (service sched j t) = true) →
    scheduled_at sched j t = true

def execution_starts_with_preemption_point (j : Job) : Prop :=
  ∀ prt,
    ¬(scheduled_at sched j prt = true) →
    scheduled_at sched j (prt + 1) = true →
    job_preemptable j (service sched j (prt + 1)) = true

def valid_preemption_model : Prop :=
  ∀ j,
    arrives_in arr_seq j →
    job_cannot_become_nonpreemptive_before_execution j
    ∧ job_cannot_be_nonpreemptive_after_completion j
    ∧ not_preemptive_implies_scheduled sched j
    ∧ execution_starts_with_preemption_point sched j

end PreemptionModel

end Prosa.Model.Preemption.Parameter
