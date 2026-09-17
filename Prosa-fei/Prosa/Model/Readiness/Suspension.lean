-- Translated from: ../rt-proofs/model/readiness/suspension.v
import Prosa.Behavior.All
import Prosa.Analysis.Definitions.Progress
import Prosa.Util.Nat

namespace Prosa.Model.Readiness.Suspension

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Ready
open Prosa.Behavior.Arrival_sequence
open Prosa.Analysis.Definitions.Progress

/-- A job's self-suspension parameter: after having received a given number of
    units of service, a job may self-suspend for a given duration, or remain
    ready if the suspension duration is zero. -/
class JobSuspension (Job : JobType) where
  job_suspension : Job → work → duration

export JobSuspension (job_suspension)

section ReadinessOfSelfSuspendingJobs

variable {Job : JobType}
variable {PState : Type _}
variable [ProcessorState Job PState]
variable [JobArrival Job] [JobCost Job] [JobSuspension Job]

/-- A job's last suspension of length `delay` has passed at time `t` if the
    job arrived at least `delay` time units ago and has not progressed within
    the last `delay` time units. -/
noncomputable def suspension_has_passed (sched : schedule PState) (j : Job) (t : instant) : Bool :=
  let delay := job_suspension j (service sched j t)
  Nat.ble (job_arrival j + delay) t && no_progress_for sched j t delay

/-- Readiness for self-suspending jobs: a job is ready at time `t` only if
    its last suspension has passed and it is not yet complete. -/
noncomputable instance suspension_ready_instance : JobReady Job PState where
  job_ready sched j t :=
    suspension_has_passed sched j t && ! Nat.ble (job_cost j) (service sched j t)
  ready_implies_pending := by
    intro sched j t h
    simp only [suspension_has_passed] at h
    simp only [Bool.and_eq_true, Bool.not_eq_true_eq_eq_false] at h
    obtain ⟨⟨hble, _⟩, hnotcomplete⟩ := h
    constructor
    · simp only [has_arrived]
      have h1 := Nat.ble_eq.mp hble
      exact Nat.le_of_add_right_le h1
    · simp only [completed_by]
      intro hge
      have : Nat.ble (job_cost j) (service sched j t) = true := Nat.ble_eq.mpr hge
      rw [this] at hnotcomplete
      exact Bool.noConfusion hnotcomplete

end ReadinessOfSelfSuspendingJobs

section TotalSuspensionTime

variable {Job : JobType}
variable [JobCost Job] [JobSuspension Job]

/-- A job's total self-suspension length is the sum of the lengths of all its
    suspensions. -/
noncomputable def total_suspension (j : Job) : duration :=
  ∑ ρ ∈ Finset.range (job_cost j), job_suspension j ρ

end TotalSuspensionTime

end Prosa.Model.Readiness.Suspension
