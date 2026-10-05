-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/sbf/plain.v

import Prosa.Analysis.Definitions.Sbf.Pred

namespace Prosa.Analysis.Definitions.Sbf.Plain

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Processor.Supply
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred

universe u v w

section SupplyBoundFunctions

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

/-- Plain SBF semantics are predicate-SBF semantics with a universally true
interval predicate. -/
noncomputable def supply_bound_function_respected
    (SBF : duration → work) : Prop :=
  pred_sbf_respected arr_seq sched (fun _ _ _ => True) SBF

/-- Plain SBF validity is predicate-SBF validity under the same predicate. -/
noncomputable def valid_supply_bound_function
    (SBF : duration → work) : Prop :=
  valid_pred_sbf arr_seq sched (fun _ _ _ => True) SBF

variable {SBF : SupplyBoundFunction}

/-- The plain bound gives the full interval's cumulative supply. -/
theorem sbf_respected_simplified
    (hbound : supply_bound_function_respected arr_seq sched
      SBF.supply_bound_function) :
    ∀ (j : Job) (t1 t2 : instant),
      arrives_in arr_seq j →
      t1 ≤ t2 →
      SBF.supply_bound_function (t2 - t1) ≤ supply_during sched t1 t2 := by
  intro j t1 t2 harr hle
  exact hbound j t1 t2 harr trivial t2 ⟨hle, Nat.le_refl _⟩

end SupplyBoundFunctions

end Prosa.Analysis.Definitions.Sbf.Plain
