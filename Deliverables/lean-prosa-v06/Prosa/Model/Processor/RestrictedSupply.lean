-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/restricted_supply.v

import Prosa.Behavior.All

namespace Prosa.Model.Processor.RestrictedSupply

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time

universe u

/-- The four source states, preserving the distinction between being idle,
executing a job, and lacking supply with or without a scheduled job. -/
inductive processor_state (Job : JobType) where
  | Idle
  | Active (j : Job)
  | Unavailable (j : Job)
  | Inactive
  deriving DecidableEq

/-- A job is scheduled in both `Active` and `Unavailable` states. -/
def rs_scheduled_on {Job : JobType} [DecidableEq Job]
    (j : Job) (s : processor_state Job) : Bool :=
  match s with
  | .Idle | .Inactive => false
  | .Active j' | .Unavailable j' => decide (j' = j)

/-- Idle and active states offer one unit of supply; unavailable states offer
none. -/
def rs_supply_on {Job : JobType} [DecidableEq Job]
    (s : processor_state Job) : work :=
  match s with
  | .Idle | .Active _ => 1
  | .Unavailable _ | .Inactive => 0

/-- Only the matching actively executing job receives service. -/
def rs_service_on {Job : JobType} [DecidableEq Job]
    (j : Job) (s : processor_state Job) : work :=
  match s with
  | .Active j' => if decide (j' = j) then 1 else 0
  | .Idle | .Unavailable _ | .Inactive => 0

/-- The complete source processor-state interface, with the Unit core and
both laws. -/
def rs_processor_state (Job : JobType) [DecidableEq Job] : ProcessorState Job where
  State := processor_state Job
  Core := Unit
  coreFintype := inferInstance
  coreDecidableEq := inferInstance
  scheduled_on j s _ := rs_scheduled_on j s
  supply_on s _ := rs_supply_on s
  service_on j s _ := rs_service_on j s
  service_on_le_supply_on := by
    intro j s r
    cases s with
    | Idle => simp [rs_service_on, rs_supply_on]
    | Active j' =>
        by_cases h : j' = j <;> simp [rs_service_on, rs_supply_on, h]
    | Unavailable j' => simp [rs_service_on, rs_supply_on]
    | Inactive => simp [rs_service_on, rs_supply_on]
  service_on_implies_scheduled_on := by
    intro j s r h
    cases s with
    | Idle => simp [rs_service_on]
    | Active j' =>
        by_cases hj : j' = j
        · simp [rs_scheduled_on, hj] at h
        · simp [rs_service_on, hj]
    | Unavailable j' => simp [rs_service_on]
    | Inactive => simp [rs_service_on]

end Prosa.Model.Processor.RestrictedSupply
