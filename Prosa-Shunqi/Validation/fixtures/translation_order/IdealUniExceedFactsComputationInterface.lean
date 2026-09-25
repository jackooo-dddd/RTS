import Prosa.Analysis.Facts.Model.IdealUniExceed

namespace Prosa.Validation.IdealUniExceedFactsInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.IdealUniExceed
open Prosa.Model.Processor.Supply
open Prosa.Analysis.Facts.Model.IdealUniExceed
open scoped BigOperators

universe u

variable {Job : JobType} [DecidableEq Job]

/-- Exact instance-specific computation of the production finite Bool fold. -/
theorem production_scheduled_in_concrete
    (j : Job) (s : exceedance_processor_state Job) :
    ProcessorState.scheduled_in (exceedance_proc_state Job) j s =
      exceedance_scheduled_on j s () := by
  change (Finset.univ : Finset Unit).fold Bool.or false
    (fun c => exceedance_scheduled_on j s c) = _
  simp

/-- Exact instance-specific computation of the production finite Nat sum. -/
theorem production_supply_in_concrete
    (s : exceedance_processor_state Job) :
    ProcessorState.supply_in (exceedance_proc_state Job) s =
      exceedance_supply_on s () := by
  change (∑ _ : Unit, exceedance_supply_on s ()) = _
  simp

theorem production_service_in_concrete
    (j : Job) (s : exceedance_processor_state Job) :
    ProcessorState.service_in (exceedance_proc_state Job) j s =
      exceedance_service_on j s () := by
  change (∑ _ : Unit, exceedance_service_on j s ()) = _
  simp

/-- The actual observer definitions, without a replacement model. -/
theorem production_scheduled_at_eq
    (sched : schedule (exceedance_proc_state Job)) (j : Job) (t : instant) :
    scheduled_at sched j t =
      ProcessorState.scheduled_in (exceedance_proc_state Job) j (sched t) :=
  rfl

theorem production_service_at_eq
    (sched : schedule (exceedance_proc_state Job)) (j : Job) (t : instant) :
    service_at sched j t =
      ProcessorState.service_in (exceedance_proc_state Job) j (sched t) :=
  rfl

theorem production_supply_at_eq
    (sched : schedule (exceedance_proc_state Job)) (t : instant) :
    supply_at sched t =
      ProcessorState.supply_in (exceedance_proc_state Job) (sched t) :=
  rfl

theorem production_is_blackout_eq
    (sched : schedule (exceedance_proc_state Job)) (t : instant) :
    is_blackout sched t =
      !decide (0 < ProcessorState.supply_in
        (exceedance_proc_state Job) (sched t)) :=
  rfl

/-- The three constructor branches of the actual production definition. -/
theorem production_is_exceedance_exec_nominal (j : Job) :
    is_exceedance_exec (.NominalExecution j) = false := rfl

theorem production_is_exceedance_exec_exceedance (j : Job) :
    is_exceedance_exec (.ExceedanceExecution j) = true := rfl

theorem production_is_exceedance_exec_idle :
    is_exceedance_exec (Job := Job) .Idle = false := rfl

end Prosa.Validation.IdealUniExceedFactsInterface
