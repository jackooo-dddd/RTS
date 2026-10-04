-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/iw_auxiliary.v

import Prosa.Analysis.Definitions.Interference
import Prosa.Analysis.Definitions.TaskSchedule
import Prosa.Analysis.Facts.Priority.Classes
import Prosa.Analysis.Abstract.RestrictedSupply.BusyPrefix
import Prosa.Model.Aggregate.ServiceOfJobs
import Prosa.Analysis.Facts.Model.ServiceOfJobs

namespace Prosa.Analysis.Abstract.IwAuxiliary

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Analysis.Abstract.Definitions
open scoped BigOperators

/-! Auxiliary properties of (conditional) interference. Binders follow the
elaborated source types: every lemma takes only the job type, the
`Interference` instance and its own inputs (the unused section context and
hypotheses are absent). Representation: the half-open sum
`\sum_(t1 <= t < t2 | P j t) F t` is `∑ t ∈ Finset.Ico t1 t2, bif P j t then F t else 0`
(the filtered big operator's own conditional body); a Boolean summand is
`Bool.toNat`; `a <= b <= c` is `(decide (a ≤ b) && decide (b ≤ c)) = true`;
`fun=> xpredT` is `fun _ _ => true`; `~~ b` is `!b`; a Boolean in `Prop`
position is `= true`. -/

section InterferenceAuxiliary

variable {Job : JobType} [DecidableEq Job] [Interference Job]

theorem fold_cumul_interference (j : Job) (t1 t2 : Nat) :
    cumul_cond_interference (fun _ _ => true) j t1 t2 = cumulative_interference j t1 t2 := rfl

theorem cumul_cond_interference_alt (P : Job → instant → Bool) (j : Job) (t1 t2 : Nat) :
    cumul_cond_interference P j t1 t2 =
      ∑ t ∈ Finset.Ico t1 t2, (bif P j t then (interference j t).toNat else 0) := by
  unfold cumul_cond_interference cond_interference
  apply Finset.sum_congr rfl
  intro t _
  cases P j t <;> rfl

theorem cumulative_interference_sub (P : Job → instant → Bool) (j : Job) (al ar bl br : instant) :
    bl ≤ al → ar ≤ br →
      cumul_cond_interference P j al ar ≤ cumul_cond_interference P j bl br := by
  intro h1 h2
  unfold cumul_cond_interference
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico h1 h2)

theorem cumulative_interference_cat (P : Job → instant → Bool) (j : Job) (t t1 t2 : Nat) :
    (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      cumul_cond_interference P j t1 t2 =
        cumul_cond_interference P j t1 t + cumul_cond_interference P j t t2 := by
  intro h
  have h' := Bool.and_eq_true_iff.mp h
  unfold cumul_cond_interference
  exact (Finset.sum_Ico_consecutive _ (of_decide_eq_true h'.1) (of_decide_eq_true h'.2)).symm

theorem cumul_cond_interference_ID (P1 P2 : Job → instant → Bool) (j : Job) (t1 t2 : Nat) :
    cumul_cond_interference P1 j t1 t2 =
      cumul_cond_interference (fun j t => P1 j t && P2 j t) j t1 t2 +
        cumul_cond_interference (fun j t => P1 j t && !P2 j t) j t1 t2 := by
  unfold cumul_cond_interference cond_interference
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t _
  dsimp only
  cases P1 j t <;> cases P2 j t <;> cases interference j t <;> rfl

theorem cumul_cond_interference_pred_eq (P1 P2 : Job → instant → Bool) (j : Job) (t1 t2 : instant) :
    (∀ (j : Job) (t : instant), P1 j t = true ↔ P2 j t = true) →
      cumul_cond_interference P1 j t1 t2 = cumul_cond_interference P2 j t1 t2 := by
  intro h
  unfold cumul_cond_interference cond_interference
  apply Finset.sum_congr rfl
  intro t _
  rw [Bool.eq_iff_iff.mpr (h j t)]

end InterferenceAuxiliary

end Prosa.Analysis.Abstract.IwAuxiliary
