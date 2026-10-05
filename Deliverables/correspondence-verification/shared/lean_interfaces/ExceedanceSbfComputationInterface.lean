import Prosa.Analysis.Facts.Model.Exceedance.SBF
import Validation.fixtures.translation_order.ExceedanceInstWitnessComputationInterface

/-!
Export root for `analysis/facts/model/exceedance/SBF.v`: the definition, the source-local SBF instance and the three
statements, together with the accepted `pi` and `sbf/busy` export roots (through the exceedance-processor
universe witnesses) and kernel-checked closed forms of the per-state observations of the exceedance processor
model.
-/

open Prosa.Behavior.Schedule Prosa.Model.Processor.IdealUniExceed Prosa.Behavior.Job

namespace Prosa.Validation.ExceedanceInterface

/- Closed forms of the per-state observations of the exceedance processor model (single `Unit` core), proved in
Lean and exported with their proofs. -/
variable {Job : JobType} [DecidableEq Job]
theorem production_exceedance_scheduled_in (j : Job) (s : (exceedance_proc_state Job).State) :
    ProcessorState.scheduled_in (exceedance_proc_state Job) j s = exceedance_scheduled_on j s () := by
  apply Bool.eq_iff_iff.2
  refine (ProcessorState.scheduled_in_eq_true_iff _ _ _).trans ⟨?_, ?_⟩
  · rintro ⟨c, hc⟩; cases c; exact hc
  · intro h; exact ⟨(), h⟩
theorem production_exceedance_service_in (j : Job) (s : (exceedance_proc_state Job).State) :
    ProcessorState.service_in (exceedance_proc_state Job) j s = exceedance_service_on j s () := rfl
theorem production_exceedance_supply_in (s : (exceedance_proc_state Job).State) :
    ProcessorState.supply_in (exceedance_proc_state Job) s = exceedance_supply_on s () := rfl
end Prosa.Validation.ExceedanceInterface
