-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/overheads.v

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Prosa.Behavior.All

namespace Prosa.Model.Processor.Overheads

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open scoped BigOperators

universe u

/-- The processor may be idle, incur one of three kinds of overhead, or make
normal progress. Both sides of a context switch may denote the idle thread. -/
inductive proc_state (Job : JobType) where
  | Idle
  | ContextSwitch (j1 j2 : Option Job)
  | Dispatch (j : Option Job)
  | CacheRelatedPreemptionDelay (j : Job)
  | Progress (j : Job)

/-- Scheduling observes the destination of a context switch, not its source. -/
def overheads_scheduled_on {Job : JobType} [DecidableEq Job]
    (j : Job) (s : proc_state Job) (_ : Unit) : Bool :=
  match s with
  | .Idle => false
  | .ContextSwitch _ none => false
  | .ContextSwitch _ (some j') => decide (j = j')
  | .Dispatch none => false
  | .Dispatch (some j') => decide (j = j')
  | .CacheRelatedPreemptionDelay j' => decide (j = j')
  | .Progress j' => decide (j = j')

/-- Idle and normal progress provide one unit of nominal supply. -/
def overheads_supply_on {Job : JobType} [DecidableEq Job]
    (s : proc_state Job) (_ : Unit) : work :=
  proc_state.casesOn (motive := fun _ => work) s
    (Nat.succ Nat.zero)
    (fun _ _ => Nat.zero)
    (fun _ => Nat.zero)
    (fun _ => Nat.zero)
    (fun _ => Nat.succ Nat.zero)

/-- Only matching normal progress yields nominal service. -/
def overheads_service_on {Job : JobType} [DecidableEq Job]
    (j : Job) (s : proc_state Job) (_ : Unit) : work :=
  proc_state.casesOn (motive := fun _ => work) s
    Nat.zero
    (fun _ _ => Nat.zero)
    (fun _ => Nat.zero)
    (fun _ => Nat.zero)
    (fun j' => if decide (j' = j) then Nat.succ Nat.zero else Nat.zero)

/-- The complete v0.6 per-core processor model, including both laws. -/
def processor_state (Job : JobType) [DecidableEq Job] : ProcessorState Job where
  State := proc_state Job
  Core := Unit
  coreFintype := inferInstance
  coreDecidableEq := inferInstance
  scheduled_on := overheads_scheduled_on
  supply_on := overheads_supply_on
  service_on := overheads_service_on
  service_on_le_supply_on := by
    intro j s r
    cases s with
    | Idle => simp [overheads_service_on, overheads_supply_on]
    | ContextSwitch j1 j2 => simp [overheads_service_on, overheads_supply_on]
    | Dispatch j' => simp [overheads_service_on, overheads_supply_on]
    | CacheRelatedPreemptionDelay j' => simp [overheads_service_on, overheads_supply_on]
    | Progress j' =>
        by_cases h : j' = j <;>
          simp [overheads_service_on, overheads_supply_on, h]
  service_on_implies_scheduled_on := by
    intro j s r h
    cases s with
    | Idle => simp [overheads_service_on]
    | ContextSwitch j1 j2 => simp [overheads_service_on]
    | Dispatch j' => simp [overheads_service_on]
    | CacheRelatedPreemptionDelay j' => simp [overheads_service_on]
    | Progress j' =>
        by_cases hsame : j' = j
        · have heq : j = j' := hsame.symm
          simp [overheads_scheduled_on, heq] at h
        · simp [overheads_service_on, hsame]

section ScheduleInspection

variable {Job : JobType} [DecidableEq Job]
variable (sched : schedule (processor_state Job))

/-- Job associated with the current processor activity, if any. -/
def scheduled_job (t : instant) : Option Job :=
  proc_state.casesOn (motive := fun _ => Option Job) (sched t)
    none
    (fun _ oj => oj)
    (fun oj => oj)
    (fun j => some j)
    (fun j => some j)

/-- The current processor activity is normal progress. -/
def is_progress (t : instant) : Bool :=
  proc_state.casesOn (motive := fun _ => Bool) (sched t)
    false (fun _ _ => false) (fun _ => false)
    (fun _ => false) (fun _ => true)

/-- The current processor activity is a context switch. -/
def is_context_switch (t : instant) : Bool :=
  proc_state.casesOn (motive := fun _ => Bool) (sched t)
    false (fun _ _ => true) (fun _ => false)
    (fun _ => false) (fun _ => false)

/-- The current processor activity is dispatch. -/
def is_dispatch (t : instant) : Bool :=
  proc_state.casesOn (motive := fun _ => Bool) (sched t)
    false (fun _ _ => false) (fun _ => true)
    (fun _ => false) (fun _ => false)

/-- The current processor activity is a cache-related preemption delay. -/
def is_CRPD (t : instant) : Bool :=
  proc_state.casesOn (motive := fun _ => Bool) (sched t)
    false (fun _ _ => false) (fun _ => false)
    (fun _ => true) (fun _ => false)

/-- Number of dispatch instants in the half-open interval `[t1, t2)`. -/
noncomputable def total_time_in_dispatch (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (is_dispatch sched t).toNat

/-- Number of context-switch instants in the half-open interval `[t1, t2)`. -/
noncomputable def total_time_in_context_switch (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (is_context_switch sched t).toNat

/-- Number of cache-related preemption-delay instants in `[t1, t2)`. -/
noncomputable def total_time_in_CRPD (t1 t2 : instant) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (is_CRPD sched t).toNat

end ScheduleInspection

end Prosa.Model.Processor.Overheads
