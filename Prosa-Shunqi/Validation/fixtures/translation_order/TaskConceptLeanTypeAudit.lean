import Prosa.Model.Task.Concept

open Prosa.Model.Task.Concept

#check @TaskType
#check @JobTask
#check @TaskDeadline
#check @TaskCost
#check @TaskMinCost
#check @task_cost_positive
#check @task_cost_at_most_deadline
#check @valid_job_cost
#check @jobs_have_valid_job_costs
#check @arrivals_have_valid_job_costs
#check @valid_min_job_cost
#check @jobs_have_valid_min_job_costs
#check @arrivals_have_valid_min_job_costs
#check @TaskSet
#check @all_jobs_from_taskset
#check @same_task
#check @same_task_sym
#check @job_of_task
#check @diff_task

#print axioms same_task_sym
#print axioms diff_task
