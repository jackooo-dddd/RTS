-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/implementation/apa/job.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 95)

import Prosa.Classic.Model.Time
import Prosa.Classic.Util.All
import Prosa.Classic.Implementation.Apa.Task

/-!
Concrete jobs of APA concrete tasks (Rocq module `ConcreteJob` of `implementation/apa/job.v`).

Representation notes (as in `classic/implementation/job.v`): the record (implicit section parameter `num_cpus`)
is a Lean structure with the same fields in the same order (`job_arrival` is `nat` in the source); `==` is
`decide (_ = _)`; the MathComp equality specification of `job_eqdef` is the informative reflection
`∀ x y, BoolReflect (x = y) (job_eqdef x y)`; the `HB.instance` registration of `hasDecEq` is the derived
`DecidableEq` instance.
-/

namespace Prosa.Classic.Implementation.Apa.Job.ConcreteJob

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Implementation.Apa.Task.ConcreteTask
open Prosa.Classic.Util.List (BoolReflect)

structure concrete_job {num_cpus : Nat} where
  job_id : Nat
  job_arrival : Nat
  job_cost : time
  job_deadline : time
  job_task : @concrete_task num_cpus
  deriving DecidableEq

def job_eqdef {num_cpus : Nat} (j1 j2 : @concrete_job num_cpus) : Bool :=
  decide (j1.job_id = j2.job_id)
  && decide (j1.job_arrival = j2.job_arrival)
  && decide (j1.job_cost = j2.job_cost)
  && decide (j1.job_deadline = j2.job_deadline)
  && decide (j1.job_task = j2.job_task)

/-- LEAN_HELPER: the Boolean observer agrees with the derived decision. -/
private theorem job_eqdef_eq_decide {num_cpus : Nat} (x y : @concrete_job num_cpus) :
    job_eqdef x y = decide (x = y) := by
  cases x; cases y
  simp only [job_eqdef, concrete_job.mk.injEq]
  simp only [Bool.decide_and, Bool.and_assoc]

def eqn_job {num_cpus : Nat} (x y : @concrete_job num_cpus) : BoolReflect (x = y) (job_eqdef x y) := by
  rw [job_eqdef_eq_decide]
  by_cases h : x = y
  · have hb : decide (x = y) = true := by simp [h]
    rw [hb]
    exact BoolReflect.isTrue h
  · have hb : decide (x = y) = false := by simp [h]
    rw [hb]
    exact BoolReflect.isFalse h

end Prosa.Classic.Implementation.Apa.Job.ConcreteJob
