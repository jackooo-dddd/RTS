-- Translated from: ../rt-proofs/classic/implementation/apa/job.v
import Prosa.Classic.Model.Time
import Prosa.Classic.Implementation.Apa.Task

namespace Prosa.Classic.Implementation.Apa.Job

namespace ConcreteJob

open Prosa.Classic.Model.Time
open Prosa.Classic.Implementation.Apa.Task.ConcreteTask

section Defs

  variable {num_cpus : ℕ}

  structure concrete_job (num_cpus : ℕ) where
    job_id : Nat
    job_arrival : Nat
    job_cost : Time
    job_deadline : Time
    job_task : concrete_task num_cpus
  deriving DecidableEq

  def job_eqdef {num_cpus : ℕ} (j1 j2 : concrete_job num_cpus) : Bool :=
    (j1.job_id == j2.job_id) &&
    (j1.job_arrival == j2.job_arrival) &&
    (j1.job_cost == j2.job_cost) &&
    (j1.job_deadline == j2.job_deadline) &&
    (j1.job_task == j2.job_task)

  theorem eqn_job {num_cpus : ℕ} (x y : concrete_job num_cpus) :
      job_eqdef x y = true ↔ x = y := by
    simp only [job_eqdef, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨⟨⟨⟨hid, harr⟩, hcost⟩, hdl⟩, htask⟩
      exact match x, y, hid, harr, hcost, hdl, htask with
      | ⟨_, _, _, _, _⟩, ⟨_, _, _, _, _⟩, rfl, rfl, rfl, rfl, rfl => rfl
    · rintro rfl
      exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

end Defs

end ConcreteJob

end Prosa.Classic.Implementation.Apa.Job
