-- Translated from: ../rt-proofs/classic/implementation/apa/task.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Apa.Affinity
import Mathlib.Data.Finset.Basic

namespace Prosa.Classic.Implementation.Apa.Task

namespace ConcreteTask

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Apa.Affinity
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset

section Defs

  variable {num_cpus : ℕ}

  structure concrete_task (num_cpus : ℕ) where
    task_id : Nat
    task_cost : Time
    task_period : Time
    task_deadline : Time
    task_affinity : affinity num_cpus
  deriving DecidableEq

  def task_eqdef {num_cpus : ℕ} (t1 t2 : concrete_task num_cpus) : Bool :=
    (t1.task_id == t2.task_id) &&
    (t1.task_cost == t2.task_cost) &&
    (t1.task_period == t2.task_period) &&
    (t1.task_deadline == t2.task_deadline) &&
    (t1.task_affinity == t2.task_affinity)

  theorem eqn_task {num_cpus : ℕ} (x y : concrete_task num_cpus) :
      task_eqdef x y = true ↔ x = y := by
    simp [task_eqdef, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨⟨⟨⟨hid, hcost⟩, hperiod⟩, hdl⟩, haff⟩
      cases x; cases y; simp_all
    · rintro rfl
      exact ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

end Defs

section ConcreteTaskset

  variable (num_cpus : ℕ)

  def concrete_taskset := Finset (concrete_task num_cpus)

end ConcreteTaskset

end ConcreteTask

end Prosa.Classic.Implementation.Apa.Task
