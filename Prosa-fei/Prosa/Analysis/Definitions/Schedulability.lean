-- Translated from: ../rt-proofs/analysis/definitions/schedulability.v
import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Model.Task.Absolute_deadline

namespace Prosa.Analysis.Definitions.Schedulability

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Absolute_deadline
open Prosa.Analysis.Facts.Behavior.Completion

section Task

variable {Task : TaskType}
variable {Job : JobType}
variable [JobArrival Job]
variable [JobCost Job]
variable [JobDeadline Job]
variable [JobTask Job Task]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)
variable (tsk : Task)
variable (R : duration)

def task_response_time_bound :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_response_time_bound sched j R

def schedulable_task :=
  ∀ j,
    arrives_in arr_seq j →
    job_task j = tsk →
    job_meets_deadline sched j

end Task

section Schedulability

variable {Task : TaskType}
variable [TaskDeadline Task]
variable {Job : JobType}
variable [JobArrival Job]
variable [JobCost Job]
variable [JobTask Job Task]
variable {PState : Type _}
variable [ProcessorState Job PState]
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule PState)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)
variable (tsk : Task)
variable (R : duration)
variable (H_R_le_deadline : R ≤ task_deadline tsk)

include H_completed_jobs_dont_execute H_R_le_deadline in
theorem schedulability_from_response_time_bound
    (H_response_time_bounded : task_response_time_bound arr_seq sched tsk R) :
    @schedulable_task Task Job _ (job_deadline_from_task_deadline Job Task) _ _ _
      arr_seq sched tsk := by
  intro j ARRj JOBtsk
  show completed_by sched j (@job_deadline Job (job_deadline_from_task_deadline Job Task) j)
  change completed_by sched j (job_arrival j + task_deadline (job_task (Task := Task) j))
  exact completion_monotonic sched j (job_arrival j + R) (job_arrival j + task_deadline (job_task j))
    (Nat.add_le_add_left (JOBtsk ▸ H_R_le_deadline) _)
    (H_response_time_bounded j ARRj JOBtsk)

end Schedulability

section AllDeadlinesMet

variable {Job : JobType}
variable [JobArrival Job]
variable [JobCost Job]
variable [JobDeadline Job]
variable {PState : Type _}
variable [DecidableEq PState]
variable [ProcessorState Job PState]

def all_deadlines_met (sched : schedule PState) :=
  ∀ (j : Job) t,
    scheduled_at sched j t = true →
    job_meets_deadline sched j

section DeadlinesOfArrivals

variable (arr_seq : arrival_sequence Job)

def all_deadlines_of_arrivals_met (sched : schedule PState) :=
  ∀ (j : Job),
    arrives_in arr_seq j →
    job_meets_deadline sched j

end DeadlinesOfArrivals

theorem all_deadlines_met_in_valid_schedule
    (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    jobs_come_from_arrival_sequence (Job := Job) sched arr_seq →
    all_deadlines_of_arrivals_met arr_seq sched →
    all_deadlines_met (Job := Job) sched := by
  intro FROM_ARR DL_ARR_MET j t SCHED
  exact DL_ARR_MET j (FROM_ARR j t SCHED)

end AllDeadlinesMet

end Prosa.Analysis.Definitions.Schedulability
