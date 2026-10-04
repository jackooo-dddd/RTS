-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/apa/task.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 76)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Apa.Affinity

/-!
Concrete tasks with processor affinities (Rocq module `ConcreteTask` of `implementation/apa/task.v`).

Representation notes (as in `classic/implementation/task.v`):
* the record `concrete_task` (implicit section parameter `num_cpus`) is a Lean structure with the same fields, in
  the same order, and the same implicit parameter `{num_cpus : Nat}`;
* `==` is `decide (_ = _)`; the MathComp equality specification of `task_eqdef` is the informative reflection
  `∀ x y, BoolReflect (x = y) (task_eqdef x y)`, a proof-valued `def`;
* the `HB.instance` registration of `hasDecEq` (Rocq's `HB_unnamed_factory_1` and the generated canonical
  `eqType` structure) is the derived `DecidableEq` instance;
* the affinity is the accepted `Affinity.affinity num_cpus` (a `Prosa.Util.Seqset.set` of processors);
* `concrete_taskset num_cpus := taskset_of (@concrete_task num_cpus)` is a reducible definition (`abbrev`).
-/

namespace Prosa.Classic.Implementation.Apa.Task.ConcreteTask

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Schedule.Apa.Affinity.Affinity (affinity)
open Prosa.Classic.Util.List (BoolReflect)

structure concrete_task {num_cpus : Nat} where
  task_id : Nat
  task_cost : time
  task_period : time
  task_deadline : time
  task_affinity : affinity num_cpus
  deriving DecidableEq

def task_eqdef {num_cpus : Nat} (t1 t2 : @concrete_task num_cpus) : Bool :=
  decide (t1.task_id = t2.task_id)
  && decide (t1.task_cost = t2.task_cost)
  && decide (t1.task_period = t2.task_period)
  && decide (t1.task_deadline = t2.task_deadline)
  && decide (t1.task_affinity = t2.task_affinity)

/-- LEAN_HELPER: the Boolean observer agrees with the derived decision. -/
private theorem task_eqdef_eq_decide {num_cpus : Nat} (x y : @concrete_task num_cpus) :
    task_eqdef x y = decide (x = y) := by
  cases x; cases y
  simp only [task_eqdef, concrete_task.mk.injEq]
  simp only [Bool.decide_and, Bool.and_assoc]

def eqn_task {num_cpus : Nat} (x y : @concrete_task num_cpus) : BoolReflect (x = y) (task_eqdef x y) := by
  rw [task_eqdef_eq_decide]
  by_cases h : x = y
  · have hb : decide (x = y) = true := by simp [h]
    rw [hb]
    exact BoolReflect.isTrue h
  · have hb : decide (x = y) = false := by simp [h]
    rw [hb]
    exact BoolReflect.isFalse h

abbrev concrete_taskset (num_cpus : Nat) : Type := taskset_of (@concrete_task num_cpus)

end Prosa.Classic.Implementation.Apa.Task.ConcreteTask
