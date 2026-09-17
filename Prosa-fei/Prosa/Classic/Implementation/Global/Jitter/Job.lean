-- Translated from: ../rt-proofs/classic/implementation/global/jitter/job.v
import Prosa.Classic.Implementation.Global.Jitter.Task

namespace Prosa.Classic.Implementation.Global.Jitter.Job

namespace ConcreteJob

open Prosa.Classic.Implementation.Global.Jitter.Task.ConcreteTask.Defs

namespace Defs

structure concrete_job where
  job_id : Nat
  job_arrival : Nat
  job_cost : Nat
  job_deadline : Nat
  job_jitter : Nat
  job_task : concrete_task
  deriving DecidableEq, Repr

def job_eqdef (j1 j2 : concrete_job) : Bool :=
  (j1.job_id == j2.job_id) &&
  (j1.job_arrival == j2.job_arrival) &&
  (j1.job_cost == j2.job_cost) &&
  (j1.job_deadline == j2.job_deadline) &&
  (j1.job_jitter == j2.job_jitter) &&
  (j1.job_task == j2.job_task)

theorem eqn_job (j1 j2 : concrete_job) :
    job_eqdef j1 j2 = true ↔ j1 = j2 := by
  constructor
  · intro h
    unfold job_eqdef at h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h6⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h5⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h4⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h, h3⟩ := h
    rw [Bool.and_eq_true] at h; obtain ⟨h1, h2⟩ := h
    rw [beq_iff_eq] at h1 h2 h3 h4 h5
    rw [beq_iff_eq] at h6
    cases j1; cases j2; subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; rfl
  · intro h; subst h; unfold job_eqdef
    simp

end Defs

end ConcreteJob

end Prosa.Classic.Implementation.Global.Jitter.Job
