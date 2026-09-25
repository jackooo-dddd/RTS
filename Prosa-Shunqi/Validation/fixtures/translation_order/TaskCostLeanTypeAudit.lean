import Prosa.Analysis.Facts.Model.TaskCost

open Prosa.Behavior.Job
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Analysis.Facts.Model.TaskCost

universe u v

#check @job_cost_positive_implies_task_cost_positive
#check @sum_job_costs_bounded

def taskCostPositiveTypeGuard
    {Task : TaskType.{u}} [DecidableEq Task]
    {Job : JobType.{v}} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] [TaskCost Task]
    (tsk : Task) (j : Job)
    (Hjob : job_of_task tsk j = true)
    (Hpos : job_cost_positive j = true)
    (Hvalid : valid_job_cost (Task := Task) j = true) :
    0 < task_cost tsk :=
  job_cost_positive_implies_task_cost_positive tsk j Hjob Hpos Hvalid

def taskCostSumTypeGuard
    {Task : TaskType.{u}} [DecidableEq Task] [TaskCost Task]
    {Job : JobType.{v}} [DecidableEq Job]
    [JobCost Job] [JobTask Job Task]
    (tsk : Task) (js : List Job)
    (Hvalid : ∀ j, j ∈ js →
      (job_of_task tsk j && valid_job_cost (Task := Task) j) = true) :
    (js.map job_cost).sum ≤ task_cost tsk * js.length :=
  sum_job_costs_bounded tsk js Hvalid

#print axioms job_cost_positive_implies_task_cost_positive
#print axioms sum_job_costs_bounded
