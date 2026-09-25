-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/varspeed.v

import Prosa.Behavior.All

namespace Prosa.Model.Processor.Varspeed

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time

universe u

/-- A variable-speed processor is either idle with unused capacity, or
executing one job at the recorded speed. -/
inductive processor_state (Job : JobType) where
  | Idle (speed : Nat)
  | Progress (j : Job) (speed : Nat)
  deriving DecidableEq

/-- A job is scheduled precisely when it matches the job in a progress state. -/
def varspeed_scheduled_on {Job : JobType} [DecidableEq Job]
    (j : Job) (s : processor_state Job) (_ : Unit) : Bool :=
  match s with
  | .Idle _ => false
  | .Progress j' _ => decide (j' = j)

/-- Both states record the amount of supply available at that instant. -/
def varspeed_supply_on {Job : JobType} [DecidableEq Job]
    (s : processor_state Job) (_ : Unit) : work :=
  match s with
  | .Idle speed | .Progress _ speed => speed

/-- A job receives the recorded speed only in a matching progress state. -/
def varspeed_service_on {Job : JobType} [DecidableEq Job]
    (j : Job) (s : processor_state Job) (_ : Unit) : work :=
  match s with
  | .Idle _ => 0
  | .Progress j' speed => if decide (j' = j) then speed else 0

/-- The complete variable-speed processor state, including its single core
and the two source laws. -/
def pstate_instance (Job : JobType) [DecidableEq Job] : ProcessorState Job where
  State := processor_state Job
  Core := Unit
  coreFintype := inferInstance
  coreDecidableEq := inferInstance
  scheduled_on j s r := varspeed_scheduled_on j s r
  supply_on s r := varspeed_supply_on s r
  service_on j s r := varspeed_service_on j s r
  service_on_le_supply_on := by
    intro j s r
    cases s with
    | Idle speed => simp [varspeed_service_on, varspeed_supply_on]
    | Progress j' speed =>
        by_cases h : j' = j <;>
          simp [varspeed_service_on, varspeed_supply_on, h]
  service_on_implies_scheduled_on := by
    intro j s r h
    cases s with
    | Idle speed => simp [varspeed_service_on]
    | Progress j' speed =>
        by_cases hj : j' = j
        · simp [varspeed_scheduled_on, hj] at h
        · simp [varspeed_service_on, hj]

end Prosa.Model.Processor.Varspeed
