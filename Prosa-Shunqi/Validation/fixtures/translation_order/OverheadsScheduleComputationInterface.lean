import Prosa.Analysis.Facts.Model.Overheads.Schedule
import Validation.fixtures.translation_order.PiComputationInterface

/-!
Export root for `analysis/facts/model/overheads/schedule.v`: the six statements together
with the accepted `pi` export root, the overheads processor model, and kernel-checked
closed forms of its per-state observations.
-/

open Prosa.Behavior.Schedule Prosa.Model.Processor.Overheads Prosa.Behavior.Job

namespace Prosa.Validation.OverheadsInterface

/- Closed forms of the per-state observations of the overheads processor
model (single `Unit` core), proved in Lean and exported with their proofs. -/
variable {Job : JobType} [DecidableEq Job]
theorem production_overheads_scheduled_in (j : Job) (s : (processor_state Job).State) :
    ProcessorState.scheduled_in (processor_state Job) j s = overheads_scheduled_on j s () := by
  apply Bool.eq_iff_iff.2
  refine (ProcessorState.scheduled_in_eq_true_iff _ _ _).trans ⟨?_, ?_⟩
  · rintro ⟨c, hc⟩; cases c; exact hc
  · intro h; exact ⟨(), h⟩
theorem production_overheads_service_in (j : Job) (s : (processor_state Job).State) :
    ProcessorState.service_in (processor_state Job) j s = overheads_service_on j s () := rfl
theorem production_overheads_supply_in (s : (processor_state Job).State) :
    ProcessorState.supply_in (processor_state Job) s = overheads_supply_on s () := rfl
end Prosa.Validation.OverheadsInterface
