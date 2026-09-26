import Prosa.Analysis.Facts.Model.Ideal.Schedule
import Validation.fixtures.translation_order.ServiceComputationInterface
import Validation.fixtures.translation_order.ArrivalSequenceComputationInterface
import Validation.fixtures.translation_order.ScheduledComputationInterface

/-!
Export root for `analysis/facts/model/ideal/schedule.v`: the nineteen facts
(statement-only) with the accepted Service/Schedule, arrival-sequence and
scheduled-job computation interfaces, plus closed-form equations for the
finite folds of the ideal (single unit core) processor state.
-/

namespace Prosa.Validation.IdealScheduleInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Model.Processor.Ideal

universe u

/-- Closed form of the production finite Boolean fold for the unit core. -/
theorem production_ideal_scheduled_in {Job : JobType.{u}} [DecidableEq Job]
    (j : Job) (s : (processor_state Job).State) :
    ProcessorState.scheduled_in (processor_state Job) j s =
      (processor_state Job).scheduled_on j s () := by
  change (Finset.univ : Finset Unit).fold Bool.or false
      (fun _ => (processor_state Job).scheduled_on j s ()) = _
  cases (processor_state Job).scheduled_on j s () <;> rfl

/-- Closed form of the production finite service sum for the unit core
(definitional: the sum over the one-element `Finset.univ`). -/
theorem production_ideal_service_in {Job : JobType.{u}} [DecidableEq Job]
    (j : Job) (s : (processor_state Job).State) :
    ProcessorState.service_in (processor_state Job) j s =
      (processor_state Job).service_on j s () := rfl

/-- Closed form of the production finite supply sum for the unit core
(definitional). -/
theorem production_ideal_supply_in {Job : JobType.{u}} [DecidableEq Job]
    (s : (processor_state Job).State) :
    ProcessorState.supply_in (processor_state Job) s =
      (processor_state Job).supply_on s () := rfl

end Prosa.Validation.IdealScheduleInterface
