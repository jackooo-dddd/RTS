-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/processor/multiprocessor.v

import Prosa.Behavior.All

namespace Prosa.Model.Processor.Multiprocessor

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open scoped BigOperators

/-! Identical multiprocessors, generic in the per-core processor state.

Representation: the ordinal type `'I_num_cpus` is `Fin num_cpus`; `\sum_(cpu < n) F cpu` is the finite sum
`∑ cpu : Fin n, F cpu`. The source's section-local instance `multiproc_state` is the named helper definition of the
same name (not a global instance); its two proof obligations are proved from the per-core facts. Binders follow the
elaborated source types: the section variables `Job`, `processor_state` and `num_cpus` are explicit. -/

section Schedule

variable (Job : JobType) [DecidableEq Job]
variable (processor_state : ProcessorState Job)

/-- The processor identifiers `0, …, num_cpus - 1`. -/
abbrev processor (num_cpus : Nat) : Type := Fin num_cpus

variable (num_cpus : Nat)

/-- A multiprocessor state maps each processor to its core-local state. -/
abbrev multiprocessor_state : Type := processor num_cpus → processor_state.State

/-- `j` is scheduled on processor `cpu` iff it is scheduled in the processor-local state. -/
def multiproc_scheduled_on (j : Job) (mps : multiprocessor_state Job processor_state num_cpus)
    (cpu : processor num_cpus) : Bool :=
  ProcessorState.scheduled_in processor_state j (mps cpu)

/-- The supply on processor `cpu` is the supply of the processor-local state. -/
noncomputable def multiproc_supply_on (mps : multiprocessor_state Job processor_state num_cpus)
    (cpu : processor num_cpus) : work :=
  ProcessorState.supply_in processor_state (mps cpu)

/-- The service of `j` on processor `cpu` is its service in the processor-local state. -/
noncomputable def multiproc_service_on (j : Job) (mps : multiprocessor_state Job processor_state num_cpus)
    (cpu : processor num_cpus) : work :=
  ProcessorState.service_in processor_state j (mps cpu)

/-- LEAN_HELPER for the source's section-local instance: the multiprocessor as a processor model whose cores are
the processors. -/
@[instance_reducible] noncomputable def multiproc_state : ProcessorState Job where
  State := multiprocessor_state Job processor_state num_cpus
  Core := processor num_cpus
  coreFintype := inferInstance
  coreDecidableEq := inferInstance
  scheduled_on := multiproc_scheduled_on Job processor_state num_cpus
  supply_on := multiproc_supply_on Job processor_state num_cpus
  service_on := multiproc_service_on Job processor_state num_cpus
  service_on_le_supply_on j mps cpu := by
    let _ := processor_state.coreFintype
    unfold multiproc_service_on multiproc_supply_on ProcessorState.service_in ProcessorState.supply_in
    exact Finset.sum_le_sum fun c _ => processor_state.service_on_le_supply_on j (mps cpu) c
  service_on_implies_scheduled_on j mps cpu h := by
    let _ := processor_state.coreFintype
    unfold multiproc_service_on ProcessorState.service_in
    unfold multiproc_scheduled_on at h
    apply Finset.sum_eq_zero
    intro c _
    apply processor_state.service_on_implies_scheduled_on
    cases hc : processor_state.scheduled_on j (mps cpu) c with
    | false => rfl
    | true =>
      have : ProcessorState.scheduled_in processor_state j (mps cpu) = true :=
        (ProcessorState.scheduled_in_eq_true_iff processor_state j (mps cpu)).mpr ⟨c, hc⟩
      rw [this] at h
      exact absurd h (by decide)

/-- The service in a multiprocessor state is the sum of the processor-local services. -/
theorem multiproc_service_in_eq :
    ∀ (j : Job) (mps : multiprocessor_state Job processor_state num_cpus),
      ProcessorState.service_in (multiproc_state Job processor_state num_cpus) j mps =
        ∑ cpu : Fin num_cpus, ProcessorState.service_in processor_state j (mps cpu) := by
  intro j mps
  rfl

end Schedule

end Prosa.Model.Processor.Multiprocessor
