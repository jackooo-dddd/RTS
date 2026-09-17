-- Translated from: ../rt-proofs/classic/implementation/uni/susp/dynamic/job.v
import Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task

namespace Prosa.Classic.Implementation.Uni.Susp.Dynamic.Job

namespace ConcreteJob

  open Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task.ConcreteTask

  section Defs

    structure concrete_job where
      job_id : Nat
      job_arrival : Nat
      job_cost : Nat
      job_deadline : Nat
      job_task : concrete_task
    deriving DecidableEq

    def job_eqdef (j1 j2 : concrete_job) : Bool :=
      (j1.job_id == j2.job_id) &&
      (j1.job_arrival == j2.job_arrival) &&
      (j1.job_cost == j2.job_cost) &&
      (j1.job_deadline == j2.job_deadline) &&
      (j1.job_task == j2.job_task)

    lemma eqn_job (j1 j2 : concrete_job) : job_eqdef j1 j2 = true ↔ j1 = j2 := by
      simp [job_eqdef, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
        cases j1; cases j2; simp_all
      · rintro rfl; exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

  end Defs

end ConcreteJob

end Prosa.Classic.Implementation.Uni.Susp.Dynamic.Job
