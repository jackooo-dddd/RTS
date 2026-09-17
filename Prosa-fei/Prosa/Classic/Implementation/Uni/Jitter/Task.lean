-- Translated from: ../rt-proofs/classic/implementation/uni/jitter/task.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Mathlib.Data.Finset.Basic

namespace Prosa.Classic.Implementation.Uni.Jitter.Task

namespace ConcreteTask

open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset

section Defs

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
    cases t1 with | mk id1 cost1 period1 deadline1 jitter1 => ?_
    cases t2 with | mk id2 cost2 period2 deadline2 jitter2 => ?_
    simp only [task_eqdef, Bool.and_eq_true, concrete_task.mk.injEq]
    constructor
    · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | (revert h1; exact of_decide_eq_true)
                                             | (revert h2; exact of_decide_eq_true)
                                             | (revert h3; exact of_decide_eq_true)
                                             | (revert h4; exact of_decide_eq_true)
                                             | (revert h5; exact of_decide_eq_true)
    · rintro ⟨h1, h2, h3, h4, h5⟩
      subst h1; subst h2; subst h3; subst h4; subst h5
      refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> exact decide_eq_true_eq.mpr rfl

end Defs

section ConcreteTaskset

  def concrete_taskset := Finset concrete_task

end ConcreteTaskset

end ConcreteTask

end Prosa.Classic.Implementation.Uni.Jitter.Task
