-- Translated from: ../rt-proofs/model/processor/ideal.v
import Prosa.Behavior.All

namespace Prosa.Model.Processor.Ideal

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service

section State

variable (Job : JobType) [DecidableEq Job]

/-- The ideal processor state: either some job is scheduled, or the processor is idle. -/
abbrev processor_state := Option Job

/-- A job is scheduled in a given state iff the state is `some j`. -/
def ideal_scheduled_at (j : Job) (s : processor_state Job) : Bool :=
  decide (s = some j)

/-- A job receives service in a given state iff the state is `some j`. -/
def ideal_service_in (j : Job) (s : processor_state Job) : work :=
  if decide (s = some j) then 1 else 0

noncomputable instance pstate_instance : ProcessorState Job (processor_state Job) where
  Core := Unit
  Core_fintype := inferInstance
  Core_deceq := inferInstance
  scheduled_on j s _ := ideal_scheduled_at Job j s
  service_in j s := ideal_service_in Job j s
  service_implies_scheduled := by
      intro j s h
      simp [ideal_service_in]
      intro heq
      exfalso
      apply h
      exact ⟨(), by simp [ideal_scheduled_at, heq]⟩

end State

section IsIdle

variable {Job : JobType}
variable (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
variable (sched : schedule (processor_state Job))

/-- The processor is idle at time t iff there is no job being scheduled. -/
def is_idle (t : instant) : Prop := sched t = none

end IsIdle

end Prosa.Model.Processor.Ideal
