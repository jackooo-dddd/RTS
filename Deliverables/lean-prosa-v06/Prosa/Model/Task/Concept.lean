-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/concept.v

import Prosa.Behavior.All
import Prosa.Util.All

namespace Prosa.Model.Task.Concept

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time

universe u v

/-- Carrier of a source MathComp task `eqType`; `DecidableEq` is explicit at
each consuming boundary. -/
abbrev TaskType := Type u

/-- Assignment of each job to its task. -/
class JobTask (Job : JobType) [DecidableEq Job]
    (Task : TaskType) [DecidableEq Task] where
  job_task : Job → Task

export JobTask (job_task)

/-- Relative deadline of a task. -/
class TaskDeadline (Task : TaskType) [DecidableEq Task] where
  task_deadline : Task → duration

export TaskDeadline (task_deadline)

/-- Worst-case execution cost of a task. -/
class TaskCost (Task : TaskType) [DecidableEq Task] where
  task_cost : Task → duration

export TaskCost (task_cost)

/-- Best-case execution cost of a task. -/
class TaskMinCost (Task : TaskType) [DecidableEq Task] where
  task_min_cost : Task → duration

export TaskMinCost (task_min_cost)

section ModelValidity

variable {Task : TaskType} [DecidableEq Task]
variable [TaskCost Task] [TaskMinCost Task] [TaskDeadline Task]

/-- Boolean positivity test for a task's WCET. -/
def task_cost_positive (tsk : Task) : Bool :=
  decide (0 < task_cost tsk)

/-- Boolean test that WCET is no greater than the relative deadline. -/
def task_cost_at_most_deadline (tsk : Task) : Bool :=
  decide (task_cost tsk ≤ task_deadline tsk)

section JobCost

variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]

/-- Boolean test that job cost does not exceed its task's WCET. -/
def valid_job_cost (j : Job) : Bool :=
  decide (job_cost j ≤ task_cost (job_task (Task := Task) j))

/-- Every job's cost respects its task's WCET. -/
def jobs_have_valid_job_costs : Prop :=
  ∀ j : Job, valid_job_cost (Task := Task) j = true

/-- Each arriving job's cost respects its task's WCET. -/
def arrivals_have_valid_job_costs (arrSeq : arrival_sequence Job) : Prop :=
  ∀ j : Job, arrives_in arrSeq j →
    valid_job_cost (Task := Task) j = true

end JobCost

section MinJobCost

variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]

/-- Boolean test that job cost is no less than its task's BCET. -/
def valid_min_job_cost (j : Job) : Bool :=
  decide (task_min_cost (job_task (Task := Task) j) ≤ job_cost j)

/-- Every job's cost respects its task's BCET. -/
def jobs_have_valid_min_job_costs : Prop :=
  ∀ j : Job, valid_min_job_cost (Task := Task) j = true

/-- Each arriving job's cost respects its task's BCET. -/
def arrivals_have_valid_min_job_costs
    (arrSeq : arrival_sequence Job) : Prop :=
  ∀ j : Job, arrives_in arrSeq j →
    valid_min_job_cost (Task := Task) j = true

end MinJobCost

end ModelValidity

/-- A finite, ordered task set. -/
abbrev TaskSet (Task : TaskType) := List Task

section ValidTaskSet

variable {Task : TaskType} [DecidableEq Task] [TaskCost Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]

/-- Every arriving job is assigned to a task in the given task set. -/
def all_jobs_from_taskset (arrSeq : arrival_sequence Job)
    (ts : TaskSet Task) : Prop :=
  ∀ j : Job, arrives_in arrSeq j →
    decide (job_task j ∈ ts) = true

end ValidTaskSet

section SameTask

variable {Job : JobType} [DecidableEq Job]
variable {Task : TaskType} [DecidableEq Task] [JobTask Job Task]

/-- Two jobs are assigned to the same task. -/
def same_task (j1 j2 : Job) : Bool :=
  decide (job_task (Task := Task) j1 = job_task (Task := Task) j2)

/-- Task equality is symmetric. -/
theorem same_task_sym (j1 j2 : Job) :
    same_task (Task := Task) j1 j2 =
      same_task (Task := Task) j2 j1 := by
  simp [same_task, eq_comm]

/-- Job `j` is assigned to task `tsk`. -/
def job_of_task (tsk : Task) (j : Job) : Bool :=
  decide (job_task j = tsk)

/-- Jobs with different membership in a task cannot share a task. -/
theorem diff_task (tsk : Task) (j1 j2 : Job) :
    job_of_task tsk j1 = true →
    job_of_task tsk j2 = false →
    same_task (Task := Task) j1 j2 = false := by
  simp only [job_of_task, same_task, decide_eq_true_eq, decide_eq_false_iff_not]
  intro h1 h2 hsame
  exact h2 (hsame.symm.trans h1)

end SameTask

end Prosa.Model.Task.Concept
