-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/sbf/pred.v

import Prosa.Behavior.Arrival_sequence
import Prosa.Model.Processor.Supply
import Prosa.Analysis.Definitions.Sbf.Sbf
import Prosa.Util.Rel

namespace Prosa.Analysis.Definitions.Sbf.Pred

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Processor.Supply
open Prosa.Analysis.Definitions.Sbf

section PredSupplyBoundFunctions

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)
variable (P : Job → instant → instant → Prop)

/-- `SBF` lower-bounds supply on every qualifying subinterval. -/
noncomputable def pred_sbf_respected (SBF : duration → work) : Prop :=
  ∀ (j : Job) (t1 t2 : instant),
    arrives_in arr_seq j → P j t1 t2 →
    ∀ (t : instant), t1 ≤ t ∧ t ≤ t2 →
      SBF (t - t1) ≤ supply_during sched t1 t

/-- Validity requires a zero initial bound and respect of the predicate. -/
noncomputable def valid_pred_sbf (SBF : duration → work) : Prop :=
  SBF 0 = 0 ∧ pred_sbf_respected arr_seq sched P SBF

/-- Boolean-order monotonicity of the supply bound. -/
def sbf_is_monotone (SBF : duration → work) : Prop :=
  Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) SBF

/-- A unit-supply bound grows by at most one per instant. -/
def unit_supply_bound_function (SBF : duration → work) : Prop :=
  ∀ δ : duration, SBF (δ + 1) ≤ SBF δ + 1

variable {SBF : SupplyBoundFunction}

/-- A valid unit-growth supply bound cannot exceed elapsed duration. -/
theorem sbf_bounded_by_duration
    (hvalid : valid_pred_sbf arr_seq sched P SBF.supply_bound_function)
    (hunit : unit_supply_bound_function SBF.supply_bound_function)
    (δ : duration) : SBF.supply_bound_function δ ≤ δ := by
  obtain ⟨hzero, _⟩ := hvalid
  induction δ with
  | zero => simpa only [hzero, Nat.le_refl]
  | succ n ih =>
      calc
        SBF.supply_bound_function (n + 1) ≤
            SBF.supply_bound_function n + 1 := hunit n
        _ ≤ n + 1 := Nat.add_le_add_right ih 1

end PredSupplyBoundFunctions

end Prosa.Analysis.Definitions.Sbf.Pred
