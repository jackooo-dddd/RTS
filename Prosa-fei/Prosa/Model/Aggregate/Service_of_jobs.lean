-- Translated from: ../rt-proofs/model/aggregate/service_of_jobs.v
import Prosa.Model.Priority.Classes

namespace Prosa.Model.Aggregate.Service_of_jobs

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Classes

section ServiceOfJobs

variable {Task : TaskType}
variable {Job : JobType}
variable [JobTask Job Task]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)

section ServiceOfSetOfJobs

variable (P : Job → Bool)
variable (jobs : List Job)

/-- The cumulative service received at time t by jobs in jobs that satisfy predicate P. -/
noncomputable def service_of_jobs_at (t : instant) : work :=
  ((jobs.filter (fun j => P j)).map (fun j => service_at sched j t)).sum

/-- The cumulative service received during [t1, t2) by jobs that satisfy predicate P. -/
noncomputable def service_of_jobs (t1 t2 : instant) : work :=
  ((jobs.filter (fun j => P j)).map (fun j => service_during sched j t1 t2)).sum

end ServiceOfSetOfJobs

section PerJobPriority

variable [JLFP_policy Job]
variable (jobs : List Job)
variable (j : Job)

/-- The service received during [t1, t2) by jobs of higher or equal priority. -/
noncomputable def service_of_higher_or_equal_priority_jobs (t1 t2 : instant) : work :=
  service_of_jobs sched (fun j_hp => hep_job j_hp j) jobs t1 t2

end PerJobPriority

section ServiceOfTask

variable [DecidableEq Task]
variable (tsk : Task)
variable (jobs : List Job)

/-- The cumulative task service received by the jobs of task tsk within time interval [t1, t2). -/
noncomputable def task_service_of_jobs_in (t1 t2 : instant) : work :=
  service_of_jobs sched (job_of_task tsk) jobs t1 t2

end ServiceOfTask

end ServiceOfJobs

end Prosa.Model.Aggregate.Service_of_jobs
