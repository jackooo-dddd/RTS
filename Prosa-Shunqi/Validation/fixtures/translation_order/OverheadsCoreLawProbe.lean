import Prosa.Model.Processor.Overheads

/-!
Validation-only diagnostic. This deliberately does not replace the production
ProcessorState. It tests whether an explicit singleton-Core enumeration and
direct law proofs reduce the imported proof-field closure.
-/

namespace Prosa.Validation.OverheadsCoreLawProbe

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Model.Processor.Overheads

universe u

def explicitUnitDecidableEq : DecidableEq Unit :=
  fun a b => match a, b with
  | .unit, .unit => isTrue rfl

def explicitUnitFintype : Fintype Unit :=
  { elems := {()}
    complete := by
      intro x
      cases x
      decide }

def processorStateExplicitCore (Job : JobType) [DecidableEq Job] :
    ProcessorState Job where
  State := proc_state Job
  Core := Unit
  coreFintype := explicitUnitFintype
  coreDecidableEq := explicitUnitDecidableEq
  scheduled_on := overheads_scheduled_on
  supply_on := overheads_supply_on
  service_on := overheads_service_on
  service_on_le_supply_on := by
    intro j s r
    cases s with
    | Idle => simp [overheads_service_on, overheads_supply_on]
    | ContextSwitch _ _ => simp [overheads_service_on, overheads_supply_on]
    | Dispatch _ => simp [overheads_service_on, overheads_supply_on]
    | CacheRelatedPreemptionDelay _ =>
        simp [overheads_service_on, overheads_supply_on]
    | Progress j' =>
        by_cases h : j' = j <;>
          simp [overheads_service_on, overheads_supply_on, h]
  service_on_implies_scheduled_on := by
    intro j s r h
    cases s with
    | Idle => simp [overheads_service_on]
    | ContextSwitch _ _ => simp [overheads_service_on]
    | Dispatch _ => simp [overheads_service_on]
    | CacheRelatedPreemptionDelay _ => simp [overheads_service_on]
    | Progress j' =>
        by_cases hsame : j' = j
        · have heq : j = j' := hsame.symm
          simp [overheads_scheduled_on, heq] at h
        · simp [overheads_service_on, hsame]

#check processorStateExplicitCore
#print axioms explicitUnitFintype
#print axioms processorStateExplicitCore

end Prosa.Validation.OverheadsCoreLawProbe
