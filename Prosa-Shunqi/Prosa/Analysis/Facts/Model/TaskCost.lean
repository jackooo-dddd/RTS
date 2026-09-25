-- Authoritative source: Prosa v0.6, commit
-- 414e66760333eaa4ef78c685bcf53291c527a548
-- analysis/facts/model/task_cost.v

import Prosa.Behavior.All
import Prosa.Model.Job.Properties
import Prosa.Model.Task.Concept

namespace Prosa.Analysis.Facts.Model.TaskCost

open Prosa.Behavior.Job
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept

universe u v

/-- A positive job cost implies a positive WCET for the task to which the job
    belongs, provided the job respects its WCET bound. -/
theorem job_cost_positive_implies_task_cost_positive
    {Task : TaskType.{u}} [DecidableEq Task]
    {Job : JobType.{v}} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] [TaskCost Task]
    (tsk : Task) (j : Job)
    (H_job_of_task : job_of_task tsk j = true)
    (H_job_cost_positive : job_cost_positive j = true)
    (H_valid_job_cost : valid_job_cost (Task := Task) j = true) :
    0 < task_cost tsk := by
  have htask : job_task (Task := Task) j = tsk := by
    simpa [job_of_task] using H_job_of_task
  have hpositive : 0 < job_cost j := by
    simpa [job_cost_positive] using H_job_cost_positive
  have hvalid : job_cost j ≤ task_cost (job_task (Task := Task) j) := by
    simpa [valid_job_cost] using H_valid_job_cost
  exact lt_of_lt_of_le hpositive (htask ▸ hvalid)

/-- The sum of the costs of an arbitrary ordered list of jobs is bounded by
    its length times the task's WCET when every listed job is compliant. -/
theorem sum_job_costs_bounded
    {Task : TaskType.{u}} [DecidableEq Task] [TaskCost Task]
    {Job : JobType.{v}} [DecidableEq Job]
    [JobCost Job] [JobTask Job Task]
    (tsk : Task) (js : List Job)
    (H_valid_jobs : ∀ j, j ∈ js →
      (job_of_task tsk j && valid_job_cost (Task := Task) j) = true) :
    (js.map job_cost).sum ≤ task_cost tsk * js.length := by
  induction js with
  | nil => simp
  | cons j js ih =>
      have hpair : job_of_task tsk j = true ∧
          valid_job_cost (Task := Task) j = true := by
        simpa using (H_valid_jobs j (by simp))
      have htask : job_task (Task := Task) j = tsk := by
        simpa [job_of_task] using hpair.1
      have hcost : job_cost j ≤ task_cost tsk := by
        have hvalid : job_cost j ≤ task_cost (job_task (Task := Task) j) := by
          simpa [valid_job_cost] using hpair.2
        simpa [htask] using hvalid
      have htail : ∀ k, k ∈ js →
          (job_of_task tsk k && valid_job_cost (Task := Task) k) = true := by
        intro k hk
        exact H_valid_jobs k (List.mem_cons_of_mem j hk)
      have hrec := ih htail
      simpa [Nat.mul_succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
        using Nat.add_le_add hcost hrec

end Prosa.Analysis.Facts.Model.TaskCost
