-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/ideal_uni_exceed.v

import Prosa.Behavior.All

namespace Prosa.Model.Processor.IdealUniExceed

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule

universe u

/-- The three source states: nominal execution, exceedance execution, idle. -/
inductive exceedance_processor_state (Job : JobType) where
  | NominalExecution (j : Job)
  | ExceedanceExecution (j : Job)
  | Idle
  deriving DecidableEq

/-- The source's explicit Boolean equality observer. -/
def exceedance_processor_state_eqdef {Job : JobType} [DecidableEq Job]
    (p1 p2 : exceedance_processor_state Job) : Bool :=
  match p1, p2 with
  | .NominalExecution j1, .NominalExecution j2 => decide (j1 = j2)
  | .ExceedanceExecution j1, .ExceedanceExecution j2 => decide (j1 = j2)
  | .Idle, .Idle => true
  | _, _ => false

/-- LEAN_HELPER: the informative Boolean reflection view used by the source's
MathComp `Equality.axiom`. The result retains the indexed true/false cases. -/
inductive BoolReflect (P : Prop) : Bool → Type where
  | isTrue : P → BoolReflect P true
  | isFalse : (¬ P) → BoolReflect P false

private theorem eqdef_eq_decide {Job : JobType} [DecidableEq Job]
    (p1 p2 : exceedance_processor_state Job) :
    exceedance_processor_state_eqdef p1 p2 = decide (p1 = p2) := by
  cases p1 <;> cases p2 <;> simp [exceedance_processor_state_eqdef]

/-- Informative equality reflection, not merely a Prop-level iff. -/
def eqn_exceedance_processor_state {Job : JobType} [DecidableEq Job]
    (p1 p2 : exceedance_processor_state Job) :
    BoolReflect (p1 = p2) (exceedance_processor_state_eqdef p1 p2) := by
  rw [eqdef_eq_decide]
  by_cases h : p1 = p2
  · have hb : decide (p1 = p2) = true := by simp [h]
    rw [hb]
    exact BoolReflect.isTrue h
  · have hb : decide (p1 = p2) = false := by simp [h]
    rw [hb]
    exact BoolReflect.isFalse h

/-- A job is scheduled during either nominal or exceedance execution. -/
def exceedance_scheduled_on {Job : JobType} [DecidableEq Job]
    (j : Job) (proc_state : exceedance_processor_state Job) (_ : Unit) : Bool :=
  match proc_state with
  | .NominalExecution j' | .ExceedanceExecution j' => decide (j' = j)
  | .Idle => false

/-- Exceedance is a blackout for nominal supply; idle still supplies a unit. -/
def exceedance_supply_on {Job : JobType} [DecidableEq Job]
    (proc_state : exceedance_processor_state Job) (_ : Unit) : work :=
  match proc_state with
  | .NominalExecution _ => 1
  | .ExceedanceExecution _ => 0
  | .Idle => 1

/-- Only matching nominal execution yields nominal service. -/
def exceedance_service_on {Job : JobType} [DecidableEq Job]
    (j : Job) (proc_state : exceedance_processor_state Job) (_ : Unit) : work :=
  match proc_state with
  | .NominalExecution j' => if decide (j' = j) then 1 else 0
  | .ExceedanceExecution _ | .Idle => 0

/-- The complete v0.6 per-core processor-state class, including both laws. -/
instance exceedance_proc_state (Job : JobType) [DecidableEq Job] :
    ProcessorState Job where
  State := exceedance_processor_state Job
  Core := Unit
  coreFintype := inferInstance
  coreDecidableEq := inferInstance
  scheduled_on := exceedance_scheduled_on
  supply_on := exceedance_supply_on
  service_on := exceedance_service_on
  service_on_le_supply_on := by
    intro j s r
    cases s with
    | NominalExecution j' =>
        by_cases h : j' = j <;>
          simp [exceedance_service_on, exceedance_supply_on, h]
    | ExceedanceExecution j' =>
        simp [exceedance_service_on, exceedance_supply_on]
    | Idle =>
        simp [exceedance_service_on, exceedance_supply_on]
  service_on_implies_scheduled_on := by
    intro j s r h
    cases s with
    | NominalExecution j' =>
        by_cases hj : j' = j
        · simp [exceedance_scheduled_on, hj] at h
        · simp [exceedance_service_on, hj]
    | ExceedanceExecution j' =>
        simp [exceedance_service_on]
    | Idle =>
        simp [exceedance_service_on]

end Prosa.Model.Processor.IdealUniExceed
