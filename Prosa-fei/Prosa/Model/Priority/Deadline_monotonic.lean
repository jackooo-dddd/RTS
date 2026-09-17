-- Translated from: ../rt-proofs/model/priority/deadline_monotonic.v
import Prosa.Model.Priority.Classes

namespace Prosa.Model.Priority.Deadline_monotonic

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Classes

instance DM (Task : TaskType) [TaskDeadline Task] : FP_policy Task where
  hep_task := fun tsk1 tsk2 => Nat.ble (task_deadline tsk1) (task_deadline tsk2)

section Properties

  variable {Task : TaskType}
  variable [TaskDeadline Task]

  variable {Job : JobType}
  variable [JobTask Job Task]

  lemma DM_is_reflexive :
      @reflexive_priorities Job (@JLFP_to_JLDP Job (FP_to_JLFP Job Task)) := by
    intro t j
    simp [hep_job_at, hep_job, hep_task]

  lemma DM_is_transitive :
      @transitive_priorities Job (@JLFP_to_JLDP Job (FP_to_JLFP Job Task)) := by
    intro t j1 j2 j3 h1 h2
    simp [hep_job_at, hep_job, hep_task] at *
    exact Nat.le_trans h1 h2

  lemma DM_is_total :
      @total_priorities Job (@JLFP_to_JLDP Job (FP_to_JLFP Job Task)) := by
    intro t j1 j2
    simp [hep_job_at, hep_job, hep_task]
    exact Nat.le_total (task_deadline (job_task j1)) (task_deadline (job_task j2))

end Properties

end Prosa.Model.Priority.Deadline_monotonic
