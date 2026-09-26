-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/edf.v

import Prosa.Model.Priority.Classes

namespace Prosa.Model.Priority.Edf

open Prosa.Behavior.Job
open Prosa.Model.Priority.Definitions

/-- EDF: jobs ordered by absolute deadline. -/
instance EDF (Job : JobType) [DecidableEq Job] [JobDeadline Job] : JLFP_policy Job where
  hep_job j1 j2 := decide (job_deadline j1 ≤ job_deadline j2)

theorem EDF_is_reflexive {Job : JobType} [DecidableEq Job] [JobDeadline Job] :
    reflexive_job_priorities (EDF Job) :=
  fun _ => decide_eq_true (Nat.le_refl _)

theorem EDF_is_transitive {Job : JobType} [DecidableEq Job] [JobDeadline Job] :
    transitive_job_priorities (EDF Job) :=
  fun _ _ _ h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))

theorem EDF_is_total {Job : JobType} [DecidableEq Job] [JobDeadline Job] :
    total_job_priorities (EDF Job) := by
  intro x y
  show (decide (_ ≤ _) || decide (_ ≤ _)) = true
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Nat.le_total _ _

end Prosa.Model.Priority.Edf
