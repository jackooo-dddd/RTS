-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrivals.v

import Prosa.Model.Task.Concept

namespace Prosa.Model.Task.Arrivals

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Util.Notation

universe u v

section TaskArrivals

variable {Job : JobType} [DecidableEq Job]
variable {Task : TaskType} [DecidableEq Task]
variable [JobTask Job Task] [JobArrival Job] [JobCost Job]
variable (arr_seq : arrival_sequence Job) (tsk : Task)

def task_arrivals_between (t1 t2 : instant) : List Job :=
  (arrivals_between arr_seq t1 t2).filter (job_of_task tsk)

def task_arrivals_up_to (t : instant) : List Job :=
  task_arrivals_between arr_seq tsk 0 (t + 1)

def task_arrivals_before (t : instant) : List Job :=
  task_arrivals_between arr_seq tsk 0 t

def task_arrivals_at (tsk : Task) (t : instant) : List Job :=
  (arrivals_at arr_seq t).filter (job_of_task tsk)

def number_of_task_arrivals (t1 t2 : instant) : Nat :=
  (task_arrivals_between arr_seq tsk t1 t2).length

def cost_of_task_arrivals (t1 t2 : instant) : Nat :=
  ((task_arrivals_between arr_seq tsk t1 t2).map job_cost).sum

variable [JobDeadline Job]

def task_arrivals_with_deadline_within (t1 t2 : instant) : List Job :=
  (arrivals_between arr_seq t1 t2).filter (fun j =>
    job_of_task tsk j && decide (job_deadline j ≤ t2))

def number_of_task_arrivals_with_deadline_within (t1 t2 : instant) : Nat :=
  (task_arrivals_with_deadline_within arr_seq tsk t1 t2).length

end TaskArrivals

section PriorArrivals

variable {Job : JobType} [DecidableEq Job]
variable {Task : TaskType} [DecidableEq Task]
variable [JobTask Job Task] [JobArrival Job]
variable (arr_seq : arrival_sequence Job) (j : Job)

def task_arrivals_up_to_job_arrival : List Job :=
  task_arrivals_up_to arr_seq (job_task (Task := Task) j) (job_arrival j)

def task_arrivals_before_job_arrival : List Job :=
  task_arrivals_before arr_seq (job_task (Task := Task) j) (job_arrival j)

def task_arrivals_at_job_arrival : List Job :=
  task_arrivals_at arr_seq (job_task (Task := Task) j) (job_arrival j)

end PriorArrivals

section JobIndex

variable {Task : TaskType} [DecidableEq Task]
variable {Job : JobType} [DecidableEq Job]
variable [JobArrival Job] [JobTask Job Task]
variable (arr_seq : arrival_sequence Job)

def job_index (j : Job) : Nat :=
  (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j).idxOf j

end JobIndex

section PreviousJob

variable {Job : JobType} [DecidableEq Job]
variable {Task : TaskType} [DecidableEq Task]
variable [JobTask Job Task] [JobArrival Job]
variable (arr_seq : arrival_sequence Job)

def prev_job (j : Job) : Job :=
  (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j).getD
    (job_index (Task := Task) arr_seq j - 1) j

end PreviousJob

end Prosa.Model.Task.Arrivals
