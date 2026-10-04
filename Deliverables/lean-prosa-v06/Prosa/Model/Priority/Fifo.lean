-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/fifo.v

import Prosa.Model.Priority.Classes

namespace Prosa.Model.Priority.Fifo

open Prosa.Behavior.Job
open Prosa.Model.Priority.Definitions

/-- FIFO: jobs ordered by arrival time. -/
instance FIFO (Job : JobType) [DecidableEq Job] [JobArrival Job] : JLFP_policy Job where
  hep_job j1 j2 := decide (job_arrival j1 ≤ job_arrival j2)

theorem FIFO_is_reflexive {Job : JobType} [DecidableEq Job] [JobArrival Job] :
    reflexive_job_priorities (FIFO Job) :=
  fun _ => decide_eq_true (Nat.le_refl _)

theorem FIFO_is_transitive {Job : JobType} [DecidableEq Job] [JobArrival Job] :
    transitive_job_priorities (FIFO Job) :=
  fun _ _ _ h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))

theorem FIFO_is_total {Job : JobType} [DecidableEq Job] [JobArrival Job] :
    total_job_priorities (FIFO Job) := by
  intro x y
  show (decide (_ ≤ _) || decide (_ ≤ _)) = true
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

end Prosa.Model.Priority.Fifo
