-- Translated from: ../rt-proofs/classic/implementation/uni/jitter/job.v
import Prosa.Classic.Implementation.Uni.Jitter.Task

namespace Prosa.Classic.Implementation.Uni.Jitter.Job

namespace ConcreteJob

open Prosa.Classic.Implementation.Uni.Jitter.Task.ConcreteTask

section Defs

  structure concrete_job where
    job_id : Nat
    job_arrival : Nat
    job_cost : Nat
    job_deadline : Nat
    job_task : concrete_task
  deriving DecidableEq, Repr

  def job_eqdef (j1 j2 : concrete_job) : Bool :=
    (j1.job_id == j2.job_id) &&
    (j1.job_arrival == j2.job_arrival) &&
    (j1.job_cost == j2.job_cost) &&
    (j1.job_deadline == j2.job_deadline) &&
    (j1.job_task == j2.job_task)

  theorem eqn_job (j1 j2 : concrete_job) :
      job_eqdef j1 j2 = true ↔ j1 = j2 := by
    cases j1 with | mk id1 arr1 cost1 dl1 task1 => ?_
    cases j2 with | mk id2 arr2 cost2 dl2 task2 => ?_
    constructor
    · intro h
      unfold job_eqdef at h
      have hab := (Bool.and_eq_true _ _).mp h
      have hab1 := (Bool.and_eq_true _ _).mp hab.1
      have hab2 := (Bool.and_eq_true _ _).mp hab1.1
      have hab3 := (Bool.and_eq_true _ _).mp hab2.1
      have e1 := of_decide_eq_true hab3.1
      have e2 := of_decide_eq_true hab3.2
      have e3 := of_decide_eq_true hab2.2
      have e4 := of_decide_eq_true hab1.2
      have e5 := of_decide_eq_true hab.2
      subst e1; subst e2; subst e3; subst e4; subst e5
      rfl
    · intro h
      injection h with h1 h2 h3 h4 h5
      subst h1; subst h2; subst h3; subst h4; subst h5
      unfold job_eqdef
      rw [show (id1 == id1) = true from decide_eq_true_eq.mpr rfl]
      rw [show (arr1 == arr1) = true from decide_eq_true_eq.mpr rfl]
      rw [show (cost1 == cost1) = true from decide_eq_true_eq.mpr rfl]
      rw [show (dl1 == dl1) = true from decide_eq_true_eq.mpr rfl]
      rw [show (task1 == task1) = true from decide_eq_true_eq.mpr rfl]
      rfl

end Defs

end ConcreteJob

end Prosa.Classic.Implementation.Uni.Jitter.Job
