-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/SBF.v

import Prosa.Analysis.Definitions.Sbf.Pred
import Prosa.Analysis.Facts.Behavior.Supply
import Prosa.Model.Task.Concept

namespace Prosa.Analysis.Facts.SBF

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Processor.Supply
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Facts.Behavior.Supply


variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}

section SBFChangePred

variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable {SBF : SupplyBoundFunction}
variable (P1 P2 : Job → instant → instant → Prop)

theorem valid_pred_sbf_switch_predicate
    (h_p2_implies_p1 : ∀ j t1 t2,
      arrives_in arr_seq j → P2 j t1 t2 → P1 j t1 t2)
    (hvalid : valid_pred_sbf arr_seq sched P1 SBF.supply_bound_function) :
    valid_pred_sbf arr_seq sched P2 SBF.supply_bound_function := by
  rcases hvalid with ⟨hzero, hrespect⟩
  refine ⟨hzero, ?_⟩
  intro j t1 t2 harr hP2 t hinterval
  exact hrespect j t1 t2 harr (h_p2_implies_p1 j t1 t2 harr hP2) t hinterval

end SBFChangePred

section BlackoutBound

/-- Binder order follows the elaborated source type: the unit-supply
hypothesis, then `arr_seq sched P SBF`, validity, the job and its arrival,
the interval and its predicate, `Δ`, and the subinterval hypothesis. -/
theorem blackout_during_bound_SBF
    (hunit : unit_supply_proc_model PState)
    (arr_seq : arrival_sequence Job) (sched : schedule PState)
    (P : Job → instant → instant → Prop) {SBF : SupplyBoundFunction}
    (hvalid : valid_pred_sbf arr_seq sched P SBF.supply_bound_function)
    (j : Job) (harr : arrives_in arr_seq j)
    (t1 t2 : instant) (hP : P j t1 t2)
    (Δ : duration) (hsub : t1 + Δ ≤ t2) :
    blackout_during sched t1 (t1 + Δ) ≤ Δ - SBF.supply_bound_function Δ := by
  rw [blackout_during_complement sched hunit t1 Δ]
  apply Nat.sub_le_sub_left
  have hbound := (hvalid.2 j t1 t2 harr hP (t1 + Δ) ?_)
  · simpa [Nat.add_sub_cancel_left] using hbound
  · exact ⟨Nat.le_add_right t1 Δ, hsub⟩

end BlackoutBound

section UnitSupplyBoundFunctionLemmas

variable {SBF : SupplyBoundFunction}

theorem complement_SBF_monotone
    (hunit : unit_supply_bound_function SBF.supply_bound_function)
    {Δ1 Δ2 : duration} (hle : Δ1 ≤ Δ2) :
    Δ1 - SBF.supply_bound_function Δ1 ≤
      Δ2 - SBF.supply_bound_function Δ2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        Δ1 - SBF.supply_bound_function Δ1 ≤
            (Δ1 + k) - SBF.supply_bound_function (Δ1 + k) := ih
        _ ≤ (Δ1 + (k + 1)) - SBF.supply_bound_function (Δ1 + (k + 1)) := by
          have hstep :
              SBF.supply_bound_function ((Δ1 + k) + 1) ≤
                SBF.supply_bound_function (Δ1 + k) + 1 := hunit (Δ1 + k)
          have hstep' :
              SBF.supply_bound_function (Δ1 + (k + 1)) ≤
                SBF.supply_bound_function (Δ1 + k) + 1 := by
            simpa [Nat.add_assoc] using hstep
          have hcancel :
              (Δ1 + k) - SBF.supply_bound_function (Δ1 + k) =
                ((Δ1 + k) + 1) -
                  (SBF.supply_bound_function (Δ1 + k) + 1) := by
            exact (Nat.add_sub_add_right
              (Δ1 + k) 1 (SBF.supply_bound_function (Δ1 + k))).symm
          calc
            (Δ1 + k) - SBF.supply_bound_function (Δ1 + k) =
                ((Δ1 + k) + 1) -
                  (SBF.supply_bound_function (Δ1 + k) + 1) := hcancel
            _ ≤ (Δ1 + (k + 1)) -
                SBF.supply_bound_function (Δ1 + (k + 1)) := by
              simpa [Nat.add_assoc] using
                (Nat.sub_le_sub_left hstep' ((Δ1 + k) + 1))

end UnitSupplyBoundFunctionLemmas

end Prosa.Analysis.Facts.SBF
