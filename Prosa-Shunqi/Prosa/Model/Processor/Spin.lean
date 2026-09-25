-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/spin.v

import Prosa.Behavior.All

namespace Prosa.Model.Processor.Spin

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time

universe u

/-- The processor is idle, spinning on a scheduled job, or making progress on
that job. -/
inductive processor_state (Job : JobType) where
  | Idle
  | Spin (j : Job)
  | Progress (j : Job)
  deriving DecidableEq

/-- A job is scheduled while either spinning or making progress. -/
def spin_scheduled_on {Job : JobType} [DecidableEq Job]
    (j : Job) (s : processor_state Job) (_ : Unit) : Bool :=
  match s with
  | .Idle => false
  | .Spin j' | .Progress j' => decide (j' = j)

/-- Idle and progressing states offer one unit of supply; spinning offers no
supply. -/
def spin_supply_on {Job : JobType} [DecidableEq Job]
    (s : processor_state Job) (_ : Unit) : work :=
  match s with
  | .Idle | .Progress _ => 1
  | .Spin _ => 0

/-- Only a matching job in a progressing state receives service. -/
def spin_service_on {Job : JobType} [DecidableEq Job]
    (j : Job) (s : processor_state Job) (_ : Unit) : work :=
  match s with
  | .Progress j' => if decide (j' = j) then 1 else 0
  | .Idle | .Spin _ => 0

/-- The concrete source processor-state interface has a single Unit core and
retains both generic processor-state laws. -/
def pstate_instance (Job : JobType) [DecidableEq Job] : ProcessorState Job where
  State := processor_state Job
  Core := Unit
  coreFintype := inferInstance
  coreDecidableEq := inferInstance
  scheduled_on := spin_scheduled_on
  supply_on := spin_supply_on
  service_on := spin_service_on
  service_on_le_supply_on := by
    intro j s r
    cases s with
    | Idle => simp [spin_service_on, spin_supply_on]
    | Spin j' => simp [spin_service_on, spin_supply_on]
    | Progress j' =>
        by_cases h : j' = j <;> simp [spin_service_on, spin_supply_on, h]
  service_on_implies_scheduled_on := by
    intro j s r h
    cases s with
    | Idle => simp [spin_service_on]
    | Spin j' => simp [spin_service_on]
    | Progress j' =>
        by_cases hj : j' = j
        · simp [spin_scheduled_on, hj] at h
        · simp [spin_service_on, hj]

end Prosa.Model.Processor.Spin
