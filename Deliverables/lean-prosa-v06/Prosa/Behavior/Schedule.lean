-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: behavior/schedule.v

import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Prosa.Behavior.Arrival_sequence

namespace Prosa.Behavior.Schedule

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open scoped BigOperators

universe u v w

/-!
The v0.6 processor-state interface owns both its state carrier and its finite
core carrier. This intentionally differs from the historical v0.4-derived
translation, which externalized `State` and replaced the per-core service and
supply interface with an unconstrained aggregate field.
-/

/-- Generic v0.6 processor state, including its finite cores, per-core
observations, and the two source invariants. -/
class ProcessorState (Job : JobType) [DecidableEq Job] where
  State : Type v
  Core : Type w
  coreFintype : Fintype Core
  coreDecidableEq : DecidableEq Core
  scheduled_on : Job → State → Core → Bool
  supply_on : State → Core → work
  service_on : Job → State → Core → work
  service_on_le_supply_on :
    ∀ j s r, service_on j s r ≤ supply_on s r
  service_on_implies_scheduled_on :
    ∀ j s r, scheduled_on j s r = false → service_on j s r = 0

export ProcessorState
  (scheduled_on supply_on service_on service_on_le_supply_on
    service_on_implies_scheduled_on)

namespace ProcessorState

variable {Job : JobType} [DecidableEq Job]
variable (PState : ProcessorState Job)

local instance : Fintype PState.Core := PState.coreFintype
local instance : DecidableEq PState.Core := PState.coreDecidableEq

local instance : Std.Commutative Bool.or where
  comm := Bool.or_comm

local instance : Std.Associative Bool.or where
  assoc := Bool.or_assoc

/-- `LEAN_HELPER`: truth characterization of the Boolean-or fold used by
`scheduled_in`. It records the approved finite-existential interface for
actual-artifact validation and downstream proofs. -/
private theorem fold_bool_or_eq_true_iff
    {α : Type*} [DecidableEq α] (xs : Finset α) (p : α → Bool) :
    xs.fold Bool.or false p = true ↔ ∃ x ∈ xs, p x = true := by
  induction xs using Finset.induction with
  | empty => simp
  | @insert a xs ha ih =>
      rw [Finset.fold_insert ha]
      simp [ih]

/-- A job is scheduled in a state iff it is scheduled on at least one core.
The definition remains a direct Boolean computation, as in the source. -/
def scheduled_in (j : Job) (s : PState.State) : Bool :=
  (Finset.univ : Finset PState.Core).fold Bool.or false fun c =>
    PState.scheduled_on j s c

/-- `LEAN_HELPER`: reflection interface for the direct finite Boolean
computation. This helper is not an additional source declaration. -/
theorem scheduled_in_eq_true_iff (j : Job) (s : PState.State) :
    scheduled_in PState j s = true ↔
      ∃ c : PState.Core, PState.scheduled_on j s c = true := by
  simpa [scheduled_in] using
    fold_bool_or_eq_true_iff (Finset.univ : Finset PState.Core)
      (fun c => PState.scheduled_on j s c)

/-- Total supply across all cores in the given state. -/
noncomputable def supply_in (s : PState.State) : work :=
  ∑ c : PState.Core, PState.supply_on s c

/-- Total service received by a job across all cores in the given state. -/
noncomputable def service_in (j : Job) (s : PState.State) : work :=
  ∑ c : PState.Core, PState.service_on j s c

end ProcessorState

/-- A schedule maps each instant to a state of the selected processor model. -/
def schedule {Job : JobType} [DecidableEq Job]
    (PState : ProcessorState Job) :=
  instant → PState.State

end Prosa.Behavior.Schedule
