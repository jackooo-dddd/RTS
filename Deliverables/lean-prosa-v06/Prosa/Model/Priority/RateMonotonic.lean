-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/rate_monotonic.v

import Prosa.Model.Priority.Classes
import Prosa.Model.Task.Arrival.Sporadic

namespace Prosa.Model.Priority.RateMonotonic

open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Task.Arrival.Sporadic

/-- Rate-monotonic priorities: sporadic tasks ordered by minimum inter-arrival time. -/
instance RM (Task : TaskType) [DecidableEq Task] [SporadicModel Task] : FP_policy Task where
  hep_task tsk1 tsk2 := decide (task_min_inter_arrival_time tsk1 ≤ task_min_inter_arrival_time tsk2)

theorem RM_is_reflexive {Task : TaskType} [DecidableEq Task] [SporadicModel Task] :
    reflexive_task_priorities (RM Task) :=
  fun _ => decide_eq_true (Nat.le_refl _)

theorem RM_is_transitive {Task : TaskType} [DecidableEq Task] [SporadicModel Task] :
    transitive_task_priorities (RM Task) :=
  fun _ _ _ h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))

theorem RM_is_total {Task : TaskType} [DecidableEq Task] [SporadicModel Task] :
    total_task_priorities (RM Task) := by
  intro x y
  show (decide (_ ≤ _) || decide (_ ≤ _)) = true
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

end Prosa.Model.Priority.RateMonotonic
