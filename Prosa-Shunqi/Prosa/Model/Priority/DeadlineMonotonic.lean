-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/deadline_monotonic.v

import Prosa.Model.Priority.Classes

namespace Prosa.Model.Priority.DeadlineMonotonic

open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions

/-- Deadline-monotonic priorities: tasks ordered by relative deadline. -/
instance DM (Task : TaskType) [DecidableEq Task] [TaskDeadline Task] : FP_policy Task where
  hep_task tsk1 tsk2 := decide (task_deadline tsk1 ≤ task_deadline tsk2)

theorem DM_is_reflexive {Task : TaskType} [DecidableEq Task] [TaskDeadline Task] :
    reflexive_task_priorities (DM Task) :=
  fun _ => decide_eq_true (Nat.le_refl _)

theorem DM_is_transitive {Task : TaskType} [DecidableEq Task] [TaskDeadline Task] :
    transitive_task_priorities (DM Task) :=
  fun _ _ _ h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))

theorem DM_is_total {Task : TaskType} [DecidableEq Task] [TaskDeadline Task] :
    total_task_priorities (DM Task) := by
  intro x y
  show (decide (_ ≤ _) || decide (_ ≤ _)) = true
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

end Prosa.Model.Priority.DeadlineMonotonic
