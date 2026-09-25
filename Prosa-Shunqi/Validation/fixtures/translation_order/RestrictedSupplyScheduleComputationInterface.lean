import Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule

namespace Prosa.Validation.RestrictedSupplyScheduleInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.RestrictedSupply
open Prosa.Model.Processor.Supply
open scoped BigOperators

variable {Job : JobType} [DecidableEq Job]

/-- The actual restricted-supply processor's single-core Boolean fold. -/
theorem production_scheduled_in_concrete
    (j : Job) (s : processor_state Job) :
    ProcessorState.scheduled_in (rs_processor_state Job) j s =
      rs_scheduled_on j s := by
  change (Finset.univ : Finset Unit).fold Bool.or false
    (fun _ => rs_scheduled_on j s) = _
  simp

/-- The actual restricted-supply processor's single-core supply sum. -/
theorem production_supply_in_concrete
    (s : processor_state Job) :
    ProcessorState.supply_in (rs_processor_state Job) s =
      rs_supply_on s := by
  change (∑ _ : Unit, rs_supply_on s) = _
  simp

/-- The actual restricted-supply processor's single-core service sum. -/
theorem production_service_in_concrete
    (j : Job) (s : processor_state Job) :
    ProcessorState.service_in (rs_processor_state Job) j s =
      rs_service_on j s := by
  change (∑ _ : Unit, rs_service_on j s) = _
  simp

/-- Production observers, preserving their schedule and instant arguments. -/
theorem production_scheduled_at_eq
    (sched : schedule (rs_processor_state Job)) (j : Job) (t : instant) :
    scheduled_at sched j t =
      ProcessorState.scheduled_in (rs_processor_state Job) j (sched t) := rfl

theorem production_service_at_eq
    (sched : schedule (rs_processor_state Job)) (j : Job) (t : instant) :
    service_at sched j t =
      ProcessorState.service_in (rs_processor_state Job) j (sched t) := rfl

theorem production_supply_at_eq
    (sched : schedule (rs_processor_state Job)) (t : instant) :
    supply_at sched t =
      ProcessorState.supply_in (rs_processor_state Job) (sched t) := rfl

end Prosa.Validation.RestrictedSupplyScheduleInterface
