-- Translated from: ../rt-proofs/classic/implementation/uni/susp/dynamic/task.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Mathlib.Data.Finset.Basic

namespace Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task

namespace ConcreteTask

  open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset

  section Defs

    structure concrete_task where
      task_id : Nat
      task_cost : Nat
      task_period : Nat
      task_deadline : Nat
      task_suspension_bound : Nat
    deriving DecidableEq

    def task_eqdef (t1 t2 : concrete_task) : Bool :=
      (t1.task_id == t2.task_id) &&
      (t1.task_cost == t2.task_cost) &&
      (t1.task_period == t2.task_period) &&
      (t1.task_deadline == t2.task_deadline) &&
      (t1.task_suspension_bound == t2.task_suspension_bound)

    lemma eqn_task (t1 t2 : concrete_task) : task_eqdef t1 t2 = true ↔ t1 = t2 := by
      simp [task_eqdef, Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
        cases t1; cases t2; simp_all
      · rintro rfl; exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

  end Defs

  section ConcreteTaskset

    def concrete_taskset := Finset concrete_task

  end ConcreteTaskset

end ConcreteTask

end Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task
