-- Translated from: ../rt-proofs/model/processor/spin.v
import Prosa.Behavior.All

namespace Prosa.Model.Processor.Spin

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule

section State

variable (Job : JobType) [DecidableEq Job]

inductive processor_state where
  | Idle : processor_state
  | Spin (j : Job) : processor_state
  | Progress (j : Job) : processor_state

namespace processor_state

section Service

variable {Job : JobType} [DecidableEq Job]
variable (j : Job)

def spin_scheduled_on (s : processor_state Job) (_ : Unit) : Bool :=
  match s with
  | Idle => false
  | Spin j' => j' == j
  | Progress j' => j' == j

def spin_service_in (s : processor_state Job) : Nat :=
  match s with
  | Idle => 0
  | Spin _ => 0
  | Progress j' => if j' == j then 1 else 0

end Service

end processor_state

open processor_state in
instance pstate_instance {Job : JobType} [DecidableEq Job] :
    ProcessorState Job (processor_state Job) where
  Core := Unit
  Core_fintype := inferInstance
  Core_deceq := inferInstance
  scheduled_on := fun j s c => spin_scheduled_on j s c
  service_in := fun j s => spin_service_in j s
  service_implies_scheduled := by
      intro j s h
      cases s with
      | Idle => rfl
      | Spin j' => rfl
      | Progress j' =>
        simp only [spin_service_in]
        split
        · next heq =>
          exfalso
          apply h
          exact ⟨(), by simp only [spin_scheduled_on]; exact heq⟩
        · rfl

end State

end Prosa.Model.Processor.Spin
