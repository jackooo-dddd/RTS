-- Translated from: ../rt-proofs/classic/implementation/global/jitter/task.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Mathlib.Data.Finset.Basic

namespace Prosa.Classic.Implementation.Global.Jitter.Task

namespace ConcreteTask

open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset

namespace Defs

structure concrete_task where
  task_id : Nat
  task_cost : Nat
  task_period : Nat
  task_deadline : Nat
  task_jitter : Nat
  deriving DecidableEq, Repr

def task_eqdef (t1 t2 : concrete_task) : Bool :=
  (t1.task_id == t2.task_id) &&
  (t1.task_cost == t2.task_cost) &&
  (t1.task_period == t2.task_period) &&
  (t1.task_deadline == t2.task_deadline) &&
  (t1.task_jitter == t2.task_jitter)

theorem eqn_task (t1 t2 : concrete_task) :
    task_eqdef t1 t2 = true ↔ t1 = t2 := by
  constructor
  · intro h
    unfold task_eqdef at h
    have h1 := h
    rw [Bool.and_eq_true] at h1; obtain ⟨h1, h5⟩ := h1
    rw [Bool.and_eq_true] at h1; obtain ⟨h1, h4⟩ := h1
    rw [Bool.and_eq_true] at h1; obtain ⟨h1, h3⟩ := h1
    rw [Bool.and_eq_true] at h1; obtain ⟨h1, h2⟩ := h1
    rw [beq_iff_eq] at h1 h2 h3 h4 h5
    cases t1; cases t2; subst h1; subst h2; subst h3; subst h4; subst h5; rfl
  · intro h; subst h; unfold task_eqdef
    rw [beq_self_eq_true, beq_self_eq_true, beq_self_eq_true, beq_self_eq_true, beq_self_eq_true]
    rfl

end Defs

namespace ConcreteTaskset

open Defs

def concrete_taskset := Finset concrete_task

end ConcreteTaskset

end ConcreteTask

end Prosa.Classic.Implementation.Global.Jitter.Task
