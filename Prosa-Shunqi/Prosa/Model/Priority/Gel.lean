-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/priority/gel.v

import Prosa.Util.Int
import Prosa.Model.Priority.Classes

namespace Prosa.Model.Priority.Gel

open Prosa.Behavior.Job
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions

/-! Representation notes: MathComp's `int` is Lean's `Int`; `n%:R` (a natural
number cast into `int`) is the coercion `(n : Int)`; `(a <= b)%R` on `int` is
`decide (a ≤ b)`. Binder orders follow the elaborated types; the source
`#[export] Instance GEL` is a reducible definition (see below). -/

/-- A task's relative priority-point offset (an integer). -/
abbrev offset : Type := Int

/-- Each task has a constant priority-point offset. -/
class PriorityPoint (Task : TaskType) [DecidableEq Task] where
  task_priority_point : Task → offset

export PriorityPoint (task_priority_point)

/-- A job's absolute priority point: its arrival time plus its task's offset. -/
def job_priority_point {Job : JobType} [DecidableEq Job] {Task : TaskType} [DecidableEq Task]
    [JobTask Job Task] [PriorityPoint Task] [JobArrival Job] (j : Job) : Int :=
  (job_arrival j : Int) + task_priority_point (job_task (Task := Task) j)

/-- GEL: an earlier absolute priority point means higher-or-equal priority.
The source `#[export] Instance` cannot be a Lean global instance (its `Task`
parameter is not determined by the result type), so it is a reducible
definition used explicitly, as the elaborated source statements do
(`GEL Job Task`). -/
@[reducible] def GEL (Job : JobType) [DecidableEq Job] (Task : TaskType) [DecidableEq Task]
    [PriorityPoint Task] [JobArrival Job] [JobTask Job Task] : JLFP_policy Job where
  hep_job j1 j2 := decide (job_priority_point (Task := Task) j1 ≤ job_priority_point (Task := Task) j2)

theorem GEL_is_reflexive {Task : TaskType} [DecidableEq Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobTask Job Task] :
    reflexive_job_priorities (GEL Job Task) :=
  fun _ => decide_eq_true (Int.le_refl _)

theorem GEL_is_transitive {Task : TaskType} [DecidableEq Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobTask Job Task] :
    transitive_job_priorities (GEL Job Task) :=
  fun _ _ _ h1 h2 => decide_eq_true (Int.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))

theorem GEL_is_total {Task : TaskType} [DecidableEq Task] [PriorityPoint Task]
    {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobTask Job Task] :
    total_job_priorities (GEL Job Task) := by
  intro x y
  show (decide (_ ≤ _) || decide (_ ≤ _)) = true
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Int.le_total _ _

end Prosa.Model.Priority.Gel
