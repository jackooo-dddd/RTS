-- Translated from: ../rt-proofs/model/aggregate/workload.v
import Prosa.Model.Priority.Classes

namespace Prosa.Model.Aggregate.Workload

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Classes

section WorkloadOfJobs

  variable {Task : TaskType}
  variable [TaskCost Task]
  variable {Job : JobType}
  variable [JobTask Job Task]
  variable [JobCost Job]
  variable (arr_seq : arrival_sequence Job)

  section WorkloadOfJobs

    variable (P : Job → Bool)
    variable (jobs : List Job)

    /-- The total workload of the jobs that satisfy predicate P. -/
    noncomputable def workload_of_jobs : work :=
      ((jobs.filter (fun j => P j)).map (fun j => job_cost j)).sum

  end WorkloadOfJobs

  section PerJobPriority

    variable [JLFP_policy Job]
    variable (j : Job)

    /-- The workload of all jobs with higher-or-equal priority than j. -/
    noncomputable def workload_of_higher_or_equal_priority_jobs (jobs : List Job) : work :=
      workload_of_jobs (fun j_hp => hep_job j_hp j) jobs

  end PerJobPriority

  section TaskWorkload

    variable [DecidableEq Task]
    variable (tsk : Task)

    /-- The task workload as the workload of jobs of task tsk. -/
    noncomputable def task_workload (jobs : List Job) : work :=
      workload_of_jobs (job_of_task tsk) jobs

    /-- The task's workload in a given interval [t1, t2). -/
    noncomputable def task_workload_between (t1 t2 : instant) : work :=
      task_workload tsk (arrivals_between arr_seq t1 t2)

  end TaskWorkload

end WorkloadOfJobs

end Prosa.Model.Aggregate.Workload
