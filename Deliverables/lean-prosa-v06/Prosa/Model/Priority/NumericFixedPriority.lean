-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/numeric_fixed_priority.v

import Prosa.Model.Priority.Classes

namespace Prosa.Model.Priority.NumericFixedPriority

open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions

/-- A numeric priority value for each task. -/
class TaskPriority (Task : TaskType) [DecidableEq Task] where
  task_priority : Task → Nat

export TaskPriority (task_priority)

/-- `LEAN_HELPER` for the source's `#[local]` instance: larger numeric values
indicate higher priority. -/
@[instance_reducible] def NumericFPAscending (Task : TaskType) [DecidableEq Task]
    [TaskPriority Task] : FP_policy Task where
  hep_task tsk1 tsk2 := decide (task_priority tsk1 ≥ task_priority tsk2)

theorem NFPA_is_reflexive {Task : TaskType} [DecidableEq Task] [TaskPriority Task] :
    reflexive_task_priorities (NumericFPAscending Task) :=
  fun _ => decide_eq_true (Nat.le_refl _)

theorem NFPA_is_transitive {Task : TaskType} [DecidableEq Task] [TaskPriority Task] :
    transitive_task_priorities (NumericFPAscending Task) :=
  fun _ _ _ h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h2) (of_decide_eq_true h1))

theorem NFPA_is_total {Task : TaskType} [DecidableEq Task] [TaskPriority Task] :
    total_task_priorities (NumericFPAscending Task) := by
  intro x y
  show (decide (_ ≥ _) || decide (_ ≥ _)) = true
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

/-- `LEAN_HELPER` for the source's `#[local]` instance: smaller numeric values
indicate higher priority. -/
@[instance_reducible] def NumericFPDescending (Task : TaskType) [DecidableEq Task]
    [TaskPriority Task] : FP_policy Task where
  hep_task tsk1 tsk2 := decide (task_priority tsk1 ≤ task_priority tsk2)

theorem NFPD_is_reflexive {Task : TaskType} [DecidableEq Task] [TaskPriority Task] :
    reflexive_task_priorities (NumericFPDescending Task) :=
  fun _ => decide_eq_true (Nat.le_refl _)

theorem NFPD_is_transitive {Task : TaskType} [DecidableEq Task] [TaskPriority Task] :
    transitive_task_priorities (NumericFPDescending Task) :=
  fun _ _ _ h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))

theorem NFPD_is_total {Task : TaskType} [DecidableEq Task] [TaskPriority Task] :
    total_task_priorities (NumericFPDescending Task) := by
  intro x y
  show (decide (_ ≤ _) || decide (_ ≤ _)) = true
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

end Prosa.Model.Priority.NumericFixedPriority
