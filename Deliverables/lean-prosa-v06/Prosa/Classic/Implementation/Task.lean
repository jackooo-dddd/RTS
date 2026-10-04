-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/task.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 26)

import Prosa.Classic.Model.Time
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task

/-!
Concrete tasks (`time` is the classic alias of `Nat`) (Rocq module `ConcreteTask`).

Representation notes (as in the accepted v0.6 `implementation/definitions/task.v`):
* the record `concrete_task` is a Lean structure with the same fields, in the same order;
* `==` on `nat` is `decide (_ = _)`; the MathComp equality specification of `task_eqdef` (MathComp's `eq_axiom`) is the
  informative reflection `∀ x y, BoolReflect (x = y) (task_eqdef x y)`, a proof-valued `def`;
* the `HB.instance` registration of `hasDecEq` (Rocq's `HB_unnamed_factory_1` and the generated canonical
  `eqType` structure) is the derived `DecidableEq` instance;
* `concrete_taskset := taskset_of concrete_task` is a reducible definition (`abbrev`), like the Rocq
  transparent definition.
-/

namespace Prosa.Classic.Implementation.Task.ConcreteTask

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Util.List (BoolReflect)

structure concrete_task where
  task_id : Nat
  task_cost : time
  task_period : time
  task_deadline : time
  deriving DecidableEq

def task_eqdef (t1 t2 : concrete_task) : Bool :=
  decide (t1.task_id = t2.task_id)
  && decide (t1.task_cost = t2.task_cost)
  && decide (t1.task_period = t2.task_period)
  && decide (t1.task_deadline = t2.task_deadline)

/-- LEAN_HELPER: the Boolean observer agrees with the derived decision. -/
private theorem task_eqdef_eq_decide (x y : concrete_task) : task_eqdef x y = decide (x = y) := by
  cases x; cases y
  simp only [task_eqdef, concrete_task.mk.injEq]
  simp only [Bool.decide_and, Bool.and_assoc]

def eqn_task (x y : concrete_task) : BoolReflect (x = y) (task_eqdef x y) := by
  rw [task_eqdef_eq_decide]
  by_cases h : x = y
  · have hb : decide (x = y) = true := by simp [h]
    rw [hb]
    exact BoolReflect.isTrue h
  · have hb : decide (x = y) = false := by simp [h]
    rw [hb]
    exact BoolReflect.isFalse h

abbrev concrete_taskset : Type := taskset_of concrete_task

end Prosa.Classic.Implementation.Task.ConcreteTask
