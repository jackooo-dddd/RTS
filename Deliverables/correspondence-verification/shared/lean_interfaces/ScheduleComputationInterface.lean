import Prosa.Behavior.Schedule

namespace Prosa.Validation.ScheduleInterface

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open scoped BigOperators

universe u v w

variable {Job : JobType} [DecidableEq Job]
variable (PState : ProcessorState Job)

local instance : Fintype PState.Core := PState.coreFintype
local instance : DecidableEq PState.Core := PState.coreDecidableEq

/-- A validation-only ordered view of the actual `Fintype.elems` used by
`Finset.univ`.  The order is intentionally not part of the production API;
later certificates use permutation-invariant Bool-or and Nat-sum folds. -/
noncomputable def coreEnumeration : List PState.Core :=
  PState.coreFintype.elems.toList

theorem coreEnumeration_nodup :
    (coreEnumeration PState).Nodup :=
  PState.coreFintype.elems.nodup_toList

theorem coreEnumeration_complete (c : PState.Core) :
    c ∈ coreEnumeration PState := by
  exact Finset.mem_toList.mpr (PState.coreFintype.complete c)

/-- Actual-artifact truth interface for the production Boolean fold. -/
theorem production_scheduled_in_eq_true_iff
    (j : Job) (s : PState.State) :
    ProcessorState.scheduled_in PState j s = true ↔
      ∃ c : PState.Core, PState.scheduled_on j s c = true :=
  ProcessorState.scheduled_in_eq_true_iff PState j s

/-- Kernel-checkable equation exposing the production finite supply sum. -/
theorem production_supply_in_eq (s : PState.State) :
    ProcessorState.supply_in PState s =
      ∑ c : PState.Core, PState.supply_on s c :=
  rfl

/-- Kernel-checkable equation exposing the production finite service sum. -/
theorem production_service_in_eq (j : Job) (s : PState.State) :
    ProcessorState.service_in PState j s =
      ∑ c : PState.Core, PState.service_on j s c :=
  rfl

/-- Permutation-invariant list-fold interface for the actual supply sum. -/
theorem production_supply_in_as_list_sum (s : PState.State) :
    ProcessorState.supply_in PState s =
      ((coreEnumeration PState).map fun c => PState.supply_on s c).sum := by
  change
    Finset.sum PState.coreFintype.elems (fun c => PState.supply_on s c) =
      List.sum (List.map (fun c => PState.supply_on s c)
        PState.coreFintype.elems.toList)
  exact (Finset.sum_map_toList PState.coreFintype.elems
    (fun c => PState.supply_on s c)).symm

/-- Permutation-invariant list-fold interface for the actual service sum. -/
theorem production_service_in_as_list_sum (j : Job) (s : PState.State) :
    ProcessorState.service_in PState j s =
      ((coreEnumeration PState).map fun c => PState.service_on j s c).sum := by
  change
    Finset.sum PState.coreFintype.elems
        (fun c => PState.service_on j s c) =
      List.sum (List.map (fun c => PState.service_on j s c)
        PState.coreFintype.elems.toList)
  exact (Finset.sum_map_toList PState.coreFintype.elems
    (fun c => PState.service_on j s c)).symm

/-- Kernel-checkable equation for the production schedule alias. -/
theorem production_schedule_eq :
    schedule PState = (Prosa.Behavior.Time.instant → PState.State) :=
  rfl

end Prosa.Validation.ScheduleInterface
