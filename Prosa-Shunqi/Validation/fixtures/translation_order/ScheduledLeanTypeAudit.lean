import Prosa.Model.Schedule.Scheduled

-- Both source Require Exports are visible through the production module.
#check (ε : Nat)

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Schedule.Scheduled

#check @scheduled_jobs_at
#check @scheduled_job_at
#check @is_idle
#print scheduled_jobs_at
#print scheduled_job_at
#print is_idle
#print axioms scheduled_jobs_at
#print axioms scheduled_job_at
#print axioms is_idle

universe u v w
variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)
variable (t : instant)

example : scheduled_jobs_at arr_seq sched t =
    (arrivals_up_to arr_seq t).filter
      (fun j => scheduled_at sched j t) := rfl
example : scheduled_job_at arr_seq sched t =
    (scheduled_jobs_at arr_seq sched t).head? := rfl
example : is_idle arr_seq sched t =
    (scheduled_jobs_at arr_seq sched t).isEmpty := rfl
