-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/uni/susp/dynamic/job.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 35)

import Prosa.Classic.Util.All
import Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task

/-!
Concrete jobs (Rocq module `ConcreteJob`).

Representation notes (as in the accepted v0.6 `implementation/definitions/task.v` and the classic concrete
tasks): the record is a Lean structure with the same fields in the same order; `==` is `decide (_ = _)`;
the MathComp equality specification of `job_eqdef` is the informative reflection `∀ x y, BoolReflect (x = y) (job_eqdef x y)`; the
`HB.instance` registration of `hasDecEq` is the derived `DecidableEq` instance.
-/

namespace Prosa.Classic.Implementation.Uni.Susp.Dynamic.Job.ConcreteJob

open Prosa.Classic.Implementation.Uni.Susp.Dynamic.Task.ConcreteTask
open Prosa.Classic.Util.List (BoolReflect)

structure concrete_job where
  job_id : Nat
  job_arrival : Nat
  job_cost : Nat
  job_deadline : Nat
  job_task : concrete_task
  deriving DecidableEq

def job_eqdef (j1 j2 : concrete_job) : Bool :=
  decide (j1.job_id = j2.job_id)
  && decide (j1.job_arrival = j2.job_arrival)
  && decide (j1.job_cost = j2.job_cost)
  && decide (j1.job_deadline = j2.job_deadline)
  && decide (j1.job_task = j2.job_task)

/-- LEAN_HELPER: the Boolean observer agrees with the derived decision. -/
private theorem job_eqdef_eq_decide (x y : concrete_job) : job_eqdef x y = decide (x = y) := by
  cases x; cases y
  simp only [job_eqdef, concrete_job.mk.injEq]
  simp only [Bool.decide_and, Bool.and_assoc]

def eqn_job (x y : concrete_job) : BoolReflect (x = y) (job_eqdef x y) := by
  rw [job_eqdef_eq_decide]
  by_cases h : x = y
  · have hb : decide (x = y) = true := by simp [h]
    rw [hb]
    exact BoolReflect.isTrue h
  · have hb : decide (x = y) = false := by simp [h]
    rw [hb]
    exact BoolReflect.isFalse h

end Prosa.Classic.Implementation.Uni.Susp.Dynamic.Job.ConcreteJob
