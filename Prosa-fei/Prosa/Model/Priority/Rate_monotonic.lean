-- Translated from: ../rt-proofs/model/priority/rate_monotonic.v
import Prosa.Model.Priority.Classes
import Prosa.Model.Task.Arrival.Sporadic

namespace Prosa.Model.Priority.Rate_monotonic

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Classes
open Prosa.Model.Task.Arrival.Sporadic

instance RM (Task : TaskType) [SporadicModel Task] : FP_policy Task where
  hep_task := fun tsk1 tsk2 => Nat.ble (task_min_inter_arrival_time tsk1) (task_min_inter_arrival_time tsk2)

section Properties

  variable {Task : TaskType}
  variable [SporadicModel Task]

  variable {Job : JobType}
  variable [JobTask Job Task]

  lemma RM_is_reflexive :
      @reflexive_priorities Job (@JLFP_to_JLDP Job (FP_to_JLFP Job Task)) := by
    intro t j
    show Nat.ble (task_min_inter_arrival_time (job_task (Task := Task) j)) (task_min_inter_arrival_time (job_task (Task := Task) j)) = true
    exact Nat.ble_eq ▸ Nat.le_refl _

  lemma RM_is_transitive :
      @transitive_priorities Job (@JLFP_to_JLDP Job (FP_to_JLFP Job Task)) := by
    intro t j1 j2 j3 h1 h2
    change Nat.ble (task_min_inter_arrival_time (job_task (Task := Task) j1)) (task_min_inter_arrival_time (job_task (Task := Task) j2)) = true at h1
    change Nat.ble (task_min_inter_arrival_time (job_task (Task := Task) j2)) (task_min_inter_arrival_time (job_task (Task := Task) j3)) = true at h2
    show Nat.ble (task_min_inter_arrival_time (job_task (Task := Task) j1)) (task_min_inter_arrival_time (job_task (Task := Task) j3)) = true
    rw [Nat.ble_eq] at *
    exact Nat.le_trans h1 h2

  lemma RM_is_total :
      @total_priorities Job (@JLFP_to_JLDP Job (FP_to_JLFP Job Task)) := by
    intro t j1 j2
    show Nat.ble (task_min_inter_arrival_time (job_task (Task := Task) j1)) (task_min_inter_arrival_time (job_task (Task := Task) j2)) = true ∨
         Nat.ble (task_min_inter_arrival_time (job_task (Task := Task) j2)) (task_min_inter_arrival_time (job_task (Task := Task) j1)) = true
    simp only [Nat.ble_eq]
    exact Nat.le_total (task_min_inter_arrival_time (job_task (Task := Task) j1)) (task_min_inter_arrival_time (job_task (Task := Task) j2))

end Properties

end Prosa.Model.Priority.Rate_monotonic
