-- Translated from: ../rt-proofs/model/processor/multiprocessor.v
import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Prosa.Behavior.All

namespace Prosa.Model.Processor.Multiprocessor

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule

section Schedule

variable (Job : JobType)
variable (processor_state : Type _)
variable [ProcessorState Job processor_state]

/-- Given a desired number of processors `num_cpus`, we define a finite type
    of integers from 0 to `num_cpus - 1`. -/
def processor (num_cpus : Nat) := Fin num_cpus

variable (num_cpus : Nat)

/-- The "multiprocessor state" as a function that maps processor IDs
    to the given state on each core. -/
def multiprocessor_state := processor num_cpus → processor_state

/-- A given job `j` is currently scheduled on a specific processor `cpu`,
    according to the given multiprocessor state `mps`, if `j` is scheduled in
    the processor-local state `(mps cpu)`. -/
private noncomputable def multiproc_scheduled_on (j : Job) (mps : multiprocessor_state processor_state num_cpus) (cpu : processor num_cpus) : Bool :=
  ProcessorState.scheduled_in j (mps cpu)

/-- The service received by a given job `j` in a given multiprocessor state
    `mps` is given by the sum of the service received across all individual
    processors of the multiprocessor. -/
private noncomputable def multiproc_service_in (j : Job) (mps : multiprocessor_state processor_state num_cpus) : work :=
  ∑ cpu : Fin num_cpus, ProcessorState.service_in j (mps cpu)

noncomputable def service_implies_scheduled_proof
    (j : Job) (s : multiprocessor_state processor_state num_cpus)
    (h : ¬∃ c : Fin num_cpus, multiproc_scheduled_on Job processor_state num_cpus j s c = true)
    : multiproc_service_in Job processor_state num_cpus j s = 0 := by
  simp only [multiproc_service_in]
  apply Finset.sum_eq_zero
  intro cpu _
  apply ProcessorState.service_implies_scheduled
  intro ⟨c, hc⟩
  apply h
  exact ⟨cpu, by simp only [multiproc_scheduled_on, ProcessorState.scheduled_in, decide_eq_true_eq]; exact ⟨c, hc⟩⟩

/-- The multiprocessor model as an instance of `ProcessorState`. -/
noncomputable instance multiproc_state : ProcessorState Job (multiprocessor_state processor_state num_cpus) where
  Core := Fin num_cpus
  Core_fintype := Fin.fintype num_cpus
  Core_deceq := instDecidableEqFin num_cpus
  scheduled_on := multiproc_scheduled_on Job processor_state num_cpus
  service_in := multiproc_service_in Job processor_state num_cpus
  service_implies_scheduled := service_implies_scheduled_proof Job processor_state num_cpus

end Schedule

end Prosa.Model.Processor.Multiprocessor
