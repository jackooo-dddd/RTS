-- Translated from: ../rt-proofs/model/readiness/jitter.v
import Prosa.Behavior.All
import Prosa.Util.Nat

namespace Prosa.Model.Readiness.Jitter

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Ready
open Prosa.Behavior.Arrival_sequence

/-- If a job exhibits release jitter, it is not immediately available for
    execution upon arrival, and can be scheduled only after its release, which
    occurs some (bounded) time after its arrival. -/
class JobJitter (Job : JobType) where
  job_jitter : Job → duration

export JobJitter (job_jitter)

section ReadinessOfJitteryJobs

variable {Job : JobType}
variable {PState : Type _}
variable [ProcessorState Job PState]
variable [JobArrival Job] [JobCost Job] [JobJitter Job]

/-- A job is released at a time t after its arrival if the
    job's release jitter has passed. -/
def is_released (j : Job) (t : instant) : Prop :=
  job_arrival j + job_jitter j ≤ t

/-- Readiness for jobs subject to release jitter: a job is ready only if it
    is released and not yet complete. -/
noncomputable instance jitter_ready_instance : JobReady Job PState where
  job_ready sched j t :=
    Nat.ble (job_arrival j + job_jitter j) t && ! Nat.ble (job_cost j) (service sched j t)
  ready_implies_pending := by
    intro sched j t h
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false] at h
    obtain ⟨hble, hnotcomplete⟩ := h
    constructor
    · simp only [has_arrived]
      have h1 := Nat.ble_eq.mp hble
      exact Nat.le_of_add_right_le h1
    · simp only [completed_by]
      intro hge
      have : Nat.ble (job_cost j) (service sched j t) = true := Nat.ble_eq.mpr hge
      rw [this] at hnotcomplete
      exact Bool.noConfusion hnotcomplete

end ReadinessOfJitteryJobs

end Prosa.Model.Readiness.Jitter
