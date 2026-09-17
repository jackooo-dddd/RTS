-- Translated from: ../rt-proofs/model/priority/numeric_fixed_priority.v
import Prosa.Model.Priority.Classes

namespace Prosa.Model.Priority.Numeric_fixed_priority

open Prosa.Model.Priority.Classes
open Prosa.Behavior.Job
open Prosa.Model.Task.Concept

/-- A task parameter that maps each task to a numeric priority value. -/
class TaskPriority (Task : TaskType) where
  task_priority : Task → ℕ

export TaskPriority (task_priority)

/-- Numeric fixed priority: tasks are prioritized by their numeric priority values,
    where numerically smaller values indicate lower priorities. -/
@[reducible]
instance NumericFP (Task : TaskType) [TaskPriority Task] : FP_policy Task where
  hep_task := fun tsk1 tsk2 => decide (task_priority tsk1 ≥ task_priority tsk2)

section Properties

  variable {Task : TaskType}
  variable [TaskPriority Task]
  variable {Job : JobType}
  variable [JobTask Job Task]

  lemma NFP_is_reflexive :
      @reflexive_priorities Job (@JLFP_to_JLDP Job (FP_to_JLFP Job Task)) := by
    intro t j
    simp [hep_job_at, hep_job, hep_task]

  lemma NFP_is_transitive :
      @transitive_priorities Job (@JLFP_to_JLDP Job (FP_to_JLFP Job Task)) := by
    intro t j1 j2 j3 h1 h2
    simp only [hep_job_at, hep_job, hep_task] at *
    simp only [decide_eq_true_eq] at *
    omega

  lemma NFP_is_total :
      @total_priorities Job (@JLFP_to_JLDP Job (FP_to_JLFP Job Task)) := by
    intro t j1 j2
    simp only [hep_job_at, hep_job, hep_task]
    simp only [decide_eq_true_eq]
    omega

end Properties

end Prosa.Model.Priority.Numeric_fixed_priority
