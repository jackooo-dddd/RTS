-- Translated from: ../rt-proofs/model/task/concept.v
import Prosa.Behavior.All

namespace Prosa.Model.Task.Concept

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence

/-- A task type is any type with decidable equality. -/
abbrev TaskType := Type

/-- Maps each job to its corresponding task. -/
class JobTask (Job : JobType) (Task : TaskType) where
  job_task : Job → Task

export JobTask (job_task)

/-- Each task's relative deadline. -/
class TaskDeadline (Task : TaskType) where
  task_deadline : Task → duration

export TaskDeadline (task_deadline)

/-- Each task's worst-case execution cost (WCET). -/
class TaskCost (Task : TaskType) where
  task_cost : Task → duration

export TaskCost (task_cost)

section ModelValidity

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskDeadline Task]

section ValidCost

variable (tsk : Task)

/-- The WCET of the task should be positive. -/
def task_cost_positive := task_cost tsk > 0

/-- The WCET should not be larger than the deadline. -/
def task_cost_at_most_deadline := task_cost tsk ≤ task_deadline tsk

end ValidCost

section ValidJobCost

variable {Job : JobType}
variable [JobTask Job Task]
variable [JobCost Job]

/-- The cost of any job j cannot exceed the WCET of its respective task. -/
def valid_job_cost (j : Job) : Prop :=
  job_cost j ≤ task_cost (job_task (Task := Task) j)

variable (arr_seq : arrival_sequence Job)

/-- The cost of a job from the arrival sequence cannot be larger than the task cost. -/
def arrivals_have_valid_job_costs :=
  ∀ j, arrives_in arr_seq j → valid_job_cost (Task := Task) j

end ValidJobCost

end ModelValidity

/-- For simplicity, we represent sets of tasks as finite sequences. -/
abbrev TaskSet (Task : TaskType) := List Task

section ValidTaskSet

variable {Task : TaskType}
variable [TaskCost Task]
variable {Job : JobType}
variable [JobTask Job Task]
variable [JobCost Job]

variable (arr_seq : arrival_sequence Job)
variable (ts : TaskSet Task)

/-- All jobs in the arrival sequence should come from the task set. -/
def all_jobs_from_taskset :=
  ∀ j, arrives_in arr_seq j → job_task (Task := Task) j ∈ ts

end ValidTaskSet

section SameTask

variable {Job : JobType}
variable {Task : TaskType}
variable [DecidableEq Task]
variable [JobTask Job Task]

/-- Two jobs are from the same task iff job_task j1 = job_task j2. -/
def same_task (j1 j2 : Job) : Bool := job_task (Task := Task) j1 == job_task j2

/-- A job j is a job of task tsk iff job_task j = tsk. -/
def job_of_task (tsk : Task) (j : Job) : Bool := job_task j == tsk

end SameTask

end Prosa.Model.Task.Concept
