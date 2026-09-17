-- Translated from: ../rt-proofs/classic/implementation/job.v
import Prosa.Classic.Model.Time
import Prosa.Classic.Implementation.Task

namespace Prosa.Classic.Implementation.Job

namespace ConcreteJob

open Prosa.Classic.Model.Time
open Prosa.Classic.Implementation.Task.ConcreteTask

section Defs

  structure concrete_job where
    job_id : Nat
    job_arrival : Time
    job_cost : Time
    job_deadline : Time
    job_task : concrete_task
  deriving DecidableEq

  def job_eqdef (j1 j2 : concrete_job) : Bool :=
    (j1.job_id == j2.job_id) &&
    (j1.job_arrival == j2.job_arrival) &&
    (j1.job_cost == j2.job_cost) &&
    (j1.job_deadline == j2.job_deadline) &&
    (j1.job_task == j2.job_task)

  theorem eqn_job : ∀ (x y : concrete_job),
      job_eqdef x y = true ↔ x = y := by
    intro ⟨id1, a1, c1, d1, t1⟩ ⟨id2, a2, c2, d2, t2⟩
    simp only [job_eqdef, Bool.and_eq_true, beq_iff_eq, concrete_job.mk.injEq, and_assoc]

end Defs

end ConcreteJob

end Prosa.Classic.Implementation.Job
