-- Translated from: ../rt-proofs/model/processor/varspeed.v
import Prosa.Behavior.All

namespace Prosa.Model.Processor.Varspeed

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule

section State

variable (Job : JobType) [DecidableEq Job]

inductive processor_state (Job : JobType) where
  | Idle : processor_state Job
  | Progress (j : Job) (speed : Nat) : processor_state Job

section Service

variable (j : Job)

def varspeed_scheduled_on (s : processor_state Job) (_ : Unit) : Bool :=
  match s with
  | .Idle => false
  | .Progress j' _ => j' == j

def varspeed_service_in (s : processor_state Job) : work :=
  match s with
  | .Idle => 0
  | .Progress j' speed => if j' == j then speed else 0

end Service

instance pstate_instance : ProcessorState Job (processor_state Job) where
  Core := Unit
  Core_fintype := inferInstance
  Core_deceq := inferInstance
  scheduled_on := fun j s u => varspeed_scheduled_on Job j s u
  service_in := fun j s => varspeed_service_in Job j s
  service_implies_scheduled := by
    intro j s h
    unfold varspeed_service_in
    cases s with
    | Idle => rfl
    | Progress j' speed =>
      simp only [beq_iff_eq]
      split
      · next heq =>
        exfalso
        apply h
        exact ⟨(), by simp [varspeed_scheduled_on, heq]⟩
      · rfl

end State

end Prosa.Model.Processor.Varspeed
