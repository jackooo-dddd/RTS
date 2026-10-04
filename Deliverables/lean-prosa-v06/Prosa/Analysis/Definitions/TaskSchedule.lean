-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/task_schedule.v

import Prosa.Model.Task.Concept
import Prosa.Analysis.Definitions.Service
import Prosa.Model.Schedule.Scheduled

namespace Prosa.Analysis.Definitions.TaskSchedule

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Task.Concept

universe u v w

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job] [JobTask Job Task]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState)
variable (tsk : Task)

/-- Jobs of `tsk` scheduled at `t`, preserving arrival order and multiplicity. -/
def scheduled_jobs_of_task_at (t : instant) : List Job :=
  (scheduled_jobs_at arr_seq sched t).filter (fun j => job_of_task tsk j)

/-- Whether at least one job of `tsk` is scheduled at `t`. -/
def task_scheduled_at (t : instant) : Bool :=
  !(scheduled_jobs_of_task_at arr_seq sched tsk t).isEmpty

/-- Sum of the instantaneous service of scheduled jobs of `tsk`. -/
noncomputable def task_service_at (t : instant) : work :=
  (scheduled_jobs_of_task_at arr_seq sched tsk t).foldr
    (fun j total => service_at sched j t + total) 0

/-- Cumulative task service during the half-open interval `[t1, t2)`. -/
noncomputable def task_service_during (t1 t2 : instant) : work :=
  ∑ t ∈ Finset.Ico t1 t2, task_service_at arr_seq sched tsk t

/-- Cumulative task service before `t2`. -/
noncomputable def task_service (t2 : instant) : work :=
  task_service_during arr_seq sched tsk 0 t2

/-- Scheduled jobs of `tsk` that receive positive service at `t`. -/
noncomputable def served_jobs_of_task_at (t : instant) : List Job :=
  (scheduled_jobs_of_task_at arr_seq sched tsk t).filter
    (fun j => receives_service_at sched j t)

/-- Whether any job of `tsk` receives service at `t`. -/
noncomputable def task_served_at (t : instant) : Bool :=
  !(served_jobs_of_task_at arr_seq sched tsk t).isEmpty

end Prosa.Analysis.Definitions.TaskSchedule
