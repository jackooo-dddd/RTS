-- Translated from: ../rt-proofs/classic/implementation/task.v
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Mathlib.Data.Finset.Basic

namespace Prosa.Classic.Implementation.Task

namespace ConcreteTask

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset

section Defs

  structure concrete_task where
    task_id : Nat
    task_cost : Time
    task_period : Time
    task_deadline : Time
  deriving DecidableEq

  def task_eqdef (t1 t2 : concrete_task) : Bool :=
    (t1.task_id == t2.task_id) &&
    (t1.task_cost == t2.task_cost) &&
    (t1.task_period == t2.task_period) &&
    (t1.task_deadline == t2.task_deadline)

  theorem eqn_task : ∀ (x y : concrete_task),
      task_eqdef x y = true ↔ x = y := by
    intro ⟨id1, c1, p1, d1⟩ ⟨id2, c2, p2, d2⟩
    simp [task_eqdef, Bool.and_eq_true, concrete_task.mk.injEq]
    tauto

end Defs

section ConcreteTaskset

  def concrete_taskset := Finset concrete_task

end ConcreteTaskset

end ConcreteTask

end Prosa.Classic.Implementation.Task
