-- Authoritative source: Prosa v0.6, commit
-- 414e66760333eaa4ef78c685bcf53291c527a548
-- analysis/facts/model/ideal_uni_exceed.v

import Prosa.Model.Processor.IdealUniExceed
import Prosa.Model.Processor.PlatformProperties

namespace Prosa.Analysis.Facts.Model.IdealUniExceed

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.IdealUniExceed
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Processor.Supply

universe u

variable {Job : JobType} [DecidableEq Job]

private theorem supply_in_concrete
    (s : exceedance_processor_state Job) :
    ProcessorState.supply_in (exceedance_proc_state Job) s =
      exceedance_supply_on s () := by
  change (∑ _ : Unit, exceedance_supply_on s ()) = _
  simp

private theorem service_in_concrete
    (j : Job) (s : exceedance_processor_state Job) :
    ProcessorState.service_in (exceedance_proc_state Job) j s =
      exceedance_service_on j s () := by
  change (∑ _ : Unit, exceedance_service_on j s ()) = _
  simp

/-- The exceedance processor has one unit of supply in nominal and idle
    states and no supply in an exceedance state. -/
theorem eps_is_unit_supply :
    unit_supply_proc_model (exceedance_proc_state Job) := by
  intro s
  rw [supply_in_concrete]
  cases s <;> simp [exceedance_supply_on]

/-- A job is scheduled exactly in one of the two execution states carrying it. -/
theorem scheduled_at_procstate
    (sched : schedule (exceedance_proc_state Job)) (j : Job) (t : instant) :
    scheduled_at sched j t = true ↔
      sched t = .NominalExecution j ∨ sched t = .ExceedanceExecution j := by
  unfold scheduled_at
  rw [ProcessorState.scheduled_in_eq_true_iff]
  cases hstate : sched t with
  | NominalExecution j' =>
      change (∃ c : Unit, exceedance_scheduled_on j (.NominalExecution j') c = true) ↔ _
      simp [exceedance_scheduled_on]
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; rfl
  | ExceedanceExecution j' =>
      change (∃ c : Unit, exceedance_scheduled_on j (.ExceedanceExecution j') c = true) ↔ _
      simp [exceedance_scheduled_on]
      constructor
      · intro h; cases h; rfl
      · intro h; cases h; rfl
  | Idle =>
      change (∃ c : Unit, exceedance_scheduled_on j .Idle c = true) ↔ _
      simp [exceedance_scheduled_on]

/-- Two jobs scheduled on the exceedance processor at one instant coincide. -/
theorem eps_is_uniproc :
    uniprocessor_model (exceedance_proc_state Job) := by
  intro j1 j2 sched t h1 h2
  rcases (scheduled_at_procstate sched j1 t).mp h1 with h1 | h1 <;>
    rcases (scheduled_at_procstate sched j2 t).mp h2 with h2 | h2
  · cases h1.symm.trans h2
    rfl
  · cases h1.symm.trans h2
  · cases h1.symm.trans h2
  · cases h1.symm.trans h2
    rfl

/-- Every scheduled job consumes all supply in its current state. -/
theorem eps_is_fully_consuming :
    fully_consuming_proc_model (exceedance_proc_state Job) := by
  intro j sched t hscheduled
  rcases (scheduled_at_procstate sched j t).mp hscheduled with hnom | hexc
  · simp [service_at, supply_at, service_in_concrete,
      supply_in_concrete, exceedance_service_on, exceedance_supply_on, hnom]
  · simp [service_at, supply_at, service_in_concrete,
      supply_in_concrete, exceedance_service_on, exceedance_supply_on, hexc]

/-- Every job receives at most one unit of service in each processor state. -/
theorem eps_is_unit_service :
    unit_service_proc_model (exceedance_proc_state Job) := by
  intro j s
  rw [service_in_concrete]
  cases s with
  | NominalExecution j' =>
      by_cases h : j' = j <;> simp [exceedance_service_on, h]
  | ExceedanceExecution _ => simp [exceedance_service_on]
  | Idle => simp [exceedance_service_on]

/-- An exceedance execution state is the only state marked as exceedance. -/
def is_exceedance_exec (pstate : (exceedance_proc_state Job).State) : Bool :=
  match pstate with
  | .ExceedanceExecution _ => true
  | _ => false

/-- A blackout occurs exactly in an exceedance execution state. -/
theorem blackout_implies_exceedance_execution
    (sched : schedule (exceedance_proc_state Job)) (t : instant) :
    is_blackout sched t = is_exceedance_exec (sched t) := by
  unfold is_blackout has_supply supply_at
  rw [supply_in_concrete]
  cases hstate : sched t <;>
    simp [exceedance_supply_on, is_exceedance_exec]

end Prosa.Analysis.Facts.Model.IdealUniExceed
