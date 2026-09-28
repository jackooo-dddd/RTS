-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/definitions/task.v

import Prosa.Implementation.Definitions.ArrivalBound
import Prosa.Model.Task.Arrival.Curves
import Prosa.Model.Priority.NumericFixedPriority

namespace Prosa.Implementation.Definitions.Task

open Prosa.Behavior.Time
open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
open Prosa.Implementation.Definitions.ArrivalBound

/-! Reference implementations of concrete tasks and jobs.
Representation: the source's ssreflect `==` on `nat` and on the accepted
`task_arrivals_bound`/`concrete_task` equality types is `decide (_ = _)` over
the derived decidable equalities; `Equality.axiom` is the accepted informative
`BoolReflect` view (a proof-valued `def`, since it lives in `Type`, as for the
accepted `eqn_task_arrivals_bound`); the `HB.instance` registrations are the
derived `DecidableEq` instances; the global parameter instances are named
instances of the accepted classes. -/

/-- A task comprises an ID, a cost, an arrival bound, a deadline and a
priority. -/
structure concrete_task where
  task_id : Nat
  task_cost : Nat
  task_arrival : task_arrivals_bound
  task_deadline : instant
  task_priority : Nat
  deriving DecidableEq

/-- Boolean structural equality of concrete tasks. -/
def task_eqdef (t1 t2 : concrete_task) : Bool :=
  decide (t1.task_id = t2.task_id)
  && decide (t1.task_cost = t2.task_cost)
  && decide (t1.task_arrival = t2.task_arrival)
  && decide (t1.task_deadline = t2.task_deadline)
  && decide (t1.task_priority = t2.task_priority)

/-- LEAN_HELPER: the Boolean observer agrees with the derived decision. -/
private theorem task_eqdef_eq_decide (x y : concrete_task) : task_eqdef x y = decide (x = y) := by
  cases x; cases y
  simp only [task_eqdef, concrete_task.mk.injEq]
  simp only [Bool.decide_and, Bool.and_assoc]

/-- `task_eqdef` reflects equality. -/
def eqn_task (x y : concrete_task) : BoolReflect (x = y) (task_eqdef x y) := by
  rw [task_eqdef_eq_decide]
  by_cases h : x = y
  · have hb : decide (x = y) = true := by simp [h]
    rw [hb]
    exact BoolReflect.isTrue h
  · have hb : decide (x = y) = false := by simp [h]
    rw [hb]
    exact BoolReflect.isFalse h

/-- A job comprises an id, an arrival time, a cost, a deadline and its
task. -/
structure concrete_job where
  job_id : Nat
  job_arrival : instant
  job_cost : Nat
  job_deadline : instant
  job_task : concrete_task
  deriving DecidableEq

/-- The arrival-curve prefix of each possible arrival bound. -/
def get_arrival_curve_prefix (tsk : concrete_task) : ArrivalCurvePrefix :=
  match tsk.task_arrival with
  | .Periodic p => inter_arrival_to_prefix p
  | .Sporadic m => inter_arrival_to_prefix m
  | .ArrivalPrefix steps => steps

/-- The arrival bound of a concrete task. -/
def concrete_max_arrivals (tsk : concrete_task) (Δ : duration) : Nat :=
  extrapolated_arrival_curve (get_arrival_curve_prefix tsk) Δ

/-- Boolean structural equality of concrete jobs. -/
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

/-- `job_eqdef` reflects equality. -/
def eqn_job (x y : concrete_job) : BoolReflect (x = y) (job_eqdef x y) := by
  rw [job_eqdef_eq_decide]
  by_cases h : x = y
  · have hb : decide (x = y) = true := by simp [h]
    rw [hb]
    exact BoolReflect.isTrue h
  · have hb : decide (x = y) = false := by simp [h]
    rw [hb]
    exact BoolReflect.isFalse h

/-! ### Instances for concrete jobs and tasks -/

instance TaskCost : Prosa.Model.Task.Concept.TaskCost concrete_task :=
  ⟨concrete_task.task_cost⟩

instance TaskPriority : Prosa.Model.Priority.NumericFixedPriority.TaskPriority concrete_task :=
  ⟨concrete_task.task_priority⟩

instance TaskDeadline : Prosa.Model.Task.Concept.TaskDeadline concrete_task :=
  ⟨concrete_task.task_deadline⟩

instance ConcreteMaxArrivals : Prosa.Model.Task.Arrival.Curves.MaxArrivals concrete_task :=
  ⟨concrete_max_arrivals⟩

instance JobTask : Prosa.Model.Task.Concept.JobTask concrete_job concrete_task :=
  ⟨concrete_job.job_task⟩

instance JobArrival : Prosa.Behavior.Job.JobArrival concrete_job :=
  ⟨concrete_job.job_arrival⟩

instance JobCost : Prosa.Behavior.Job.JobCost concrete_job :=
  ⟨concrete_job.job_cost⟩

end Prosa.Implementation.Definitions.Task
