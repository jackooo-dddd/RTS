import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
Validation-only representation prototype for Prosa v0.6.  This file is not a
production translation and is not counted as translation coverage.
-/

namespace ProsaV06PlanningPrototype

universe u v w

abbrev instant := Nat
abbrev duration := Nat
abbrev work := Nat

/- An `eqType` carrier becomes a Lean carrier with equality evidence supplied
   separately at the declaration boundary. -/
abbrev JobType := Type u
abbrev TaskType := Type v

class JobArrival (Job : JobType) [DecidableEq Job] where
  jobArrival : Job → instant

class JobCost (Job : JobType) [DecidableEq Job] where
  jobCost : Job → work

class JobTask
    (Job : JobType) [DecidableEq Job]
    (Task : TaskType) [DecidableEq Task] where
  jobTask : Job → Task

/- Option A from the policy: State and Core remain owned by ProcessorState,
   matching the v0.6 abstraction boundary. -/
class ProcessorState (Job : JobType) [DecidableEq Job] where
  State : Type v
  Core : Type w
  coreFintype : Fintype Core
  coreDecidableEq : DecidableEq Core
  scheduledOn : Job → State → Core → Bool
  supplyOn : State → Core → work
  serviceOn : Job → State → Core → work
  serviceOnLeSupplyOn : ∀ j s r, serviceOn j s r ≤ supplyOn s r
  serviceOnImpliesScheduledOn :
    ∀ j s r, scheduledOn j s r = false → serviceOn j s r = 0

namespace ProcessorState

variable {Job : JobType} [DecidableEq Job] (PState : ProcessorState Job)

local instance : Fintype PState.Core := PState.coreFintype
local instance : DecidableEq PState.Core := PState.coreDecidableEq

local instance : Std.Commutative Bool.or where
  comm := Bool.or_comm

local instance : Std.Associative Bool.or where
  assoc := Bool.or_assoc

private theorem foldBoolOr_eq_true_iff
    {α : Type*} [DecidableEq α] (xs : Finset α) (p : α → Bool) :
    xs.fold Bool.or false p = true ↔ ∃ x ∈ xs, p x = true := by
  induction xs using Finset.induction with
  | empty => simp
  | @insert a xs ha ih =>
      rw [Finset.fold_insert ha]
      simp [ih]

def scheduledIn (j : Job) (s : PState.State) : Bool :=
  (Finset.univ : Finset PState.Core).fold Bool.or false fun c =>
    PState.scheduledOn j s c

theorem scheduledIn_eq_true_iff (j : Job) (s : PState.State) :
    scheduledIn PState j s = true ↔
      ∃ c : PState.Core, PState.scheduledOn j s c = true := by
  simpa [scheduledIn] using
    foldBoolOr_eq_true_iff (Finset.univ : Finset PState.Core)
      (fun c => PState.scheduledOn j s c)

noncomputable def supplyIn (s : PState.State) : work :=
  ∑ c : PState.Core, PState.supplyOn s c

noncomputable def serviceIn (j : Job) (s : PState.State) : work :=
  ∑ c : PState.Core, PState.serviceOn j s c

def schedule := instant → PState.State

end ProcessorState

/- `seq` and extensional finite sets remain distinct representations. -/
abbrev Seq (α : Type u) := List α
abbrev FiniteSet (α : Type u) [DecidableEq α] := Finset α

def boolPredicate (p : Nat → Bool) : Nat → Bool := p
def reflectedPredicate (p : Nat → Bool) : Nat → Prop := fun n => p n = true

theorem bool_reflection (p : Bool) : decide (p = true) = p := by
  cases p <;> rfl

end ProsaV06PlanningPrototype
