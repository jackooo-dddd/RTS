-- Translated from: ../rt-proofs/model/priority/classes.v
import Prosa.Model.Task.Concept
import Prosa.Util.Rel
import Prosa.Util.List

namespace Prosa.Model.Priority.Classes

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Util.Rel

/-- An FP policy is a relation among tasks. -/
class FP_policy (Task : TaskType) where
  hep_task : Task → Task → Bool

export FP_policy (hep_task)

/-- A JLFP policy is a relation among jobs. -/
class JLFP_policy (Job : JobType) where
  hep_job : Job → Job → Bool

export JLFP_policy (hep_job)

/-- A JLDP policy is a relation among jobs that may vary over time. -/
class JLDP_policy (Job : JobType) where
  hep_job_at : instant → Job → Job → Bool

export JLDP_policy (hep_job_at)

/-- Any FP policy can be interpreted as a JLFP policy. -/
@[reducible]
def FP_to_JLFP (Job : JobType) (Task : TaskType)
    [JobTask Job Task] [FP_policy Task] : JLFP_policy Job where
  hep_job := fun j1 j2 => hep_task (job_task (Task := Task) j1) (job_task (Task := Task) j2)

/-- Any JLFP policy implies a JLDP policy that ignores the time parameter. -/
@[reducible]
def JLFP_to_JLDP (Job : JobType) [JLFP_policy Job] : JLDP_policy Job where
  hep_job_at := fun _ j1 j2 => hep_job j1 j2

section Priorities

  variable {Task : TaskType}
  variable [TaskCost Task]
  variable {Job : JobType}
  variable [JobTask Job Task]
  variable [JobArrival Job]
  variable [JobCost Job]

  section JLDP

    variable [JLDP_policy Job]

    def reflexive_priorities :=
      ∀ t : instant, ∀ j : Job, hep_job_at t j j = true

    def transitive_priorities :=
      ∀ t : instant, ∀ j1 j2 j3 : Job,
        hep_job_at t j1 j2 = true → hep_job_at t j2 j3 = true →
        hep_job_at t j1 j3 = true

    def total_priorities :=
      ∀ t : instant, ∀ j1 j2 : Job,
        hep_job_at t j1 j2 = true ∨ hep_job_at t j2 j1 = true

  end JLDP

  section JLFP

    variable [JLFP_policy Job]

    def policy_respects_sequential_tasks [DecidableEq Task] :=
      ∀ j1 j2 : Job,
        job_task (Task := Task) j1 = job_task j2 →
        job_arrival j1 ≤ job_arrival j2 →
        hep_job j1 j2 = true

  end JLFP

  section FP

    variable [FP_policy Task]

    def antisymmetric_over_taskset [DecidableEq Task] (ts : List Task) :=
      antisymmetric_over_list hep_task ts

    theorem respects_sequential_tasks [DecidableEq Task] :
        (∀ t : instant, ∀ j : Job,
          hep_task (job_task (Task := Task) j) (job_task (Task := Task) j) = true) →
        (∀ j1 j2 : Job,
          job_task (Task := Task) j1 = job_task j2 →
          job_arrival j1 ≤ job_arrival j2 →
          hep_task (job_task (Task := Task) j1) (job_task (Task := Task) j2) = true) := by
    intro REFL j1 j2 EQ _
    rw [EQ]
    exact REFL 0 j2

  end FP

end Priorities

end Prosa.Model.Priority.Classes
