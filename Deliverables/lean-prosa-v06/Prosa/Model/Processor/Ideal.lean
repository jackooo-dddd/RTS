-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/ideal.v

import Prosa.Behavior.All

namespace Prosa.Model.Processor.Ideal

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time

universe u

/-- The ideal uniprocessor has one core and an optional scheduled job. Its
per-core supply, service, and both required laws implement the complete
v0.6 `ProcessorState` interface. -/
def processor_state (Job : JobType) [DecidableEq Job] : ProcessorState Job where
  State := Option Job
  Core := Unit
  coreFintype := inferInstance
  coreDecidableEq := inferInstance
  scheduled_on j s _ := decide (s = some j)
  supply_on _ _ := 1
  service_on j s _ := if decide (s = some j) then 1 else 0
  service_on_le_supply_on := by
    intro j s r
    by_cases h : s = some j <;> simp [h]
  service_on_implies_scheduled_on := by
    intro j s r h
    by_cases hs : s = some j
    · simp [hs] at h
    · simp [hs]

/-- An ideal processor is idle exactly when its state is `none`. The source
Section's unused arrival-sequence variable is absent from the elaborated
Rocq type, so it is not a Lean parameter. -/
def ideal_is_idle {Job : JobType} [DecidableEq Job]
    (sched : schedule (processor_state Job)) (t : instant) : Bool :=
  match sched t with
  | none => true
  | some _ => false

end Prosa.Model.Processor.Ideal
