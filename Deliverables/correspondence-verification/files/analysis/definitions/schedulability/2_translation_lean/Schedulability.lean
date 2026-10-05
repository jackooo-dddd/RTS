-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/definitions/schedulability.v

import Prosa.Analysis.Facts.Behavior.Completion
import Prosa.Model.Task.AbsoluteDeadline

namespace Prosa.Analysis.Definitions.Schedulability

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Analysis.Facts.Behavior.Completion

/-! Representation notes: a Boolean in `Prop` position is `= true`; `R <=
task_deadline tsk` in `Prop` position is the Lean proposition. The lemma
`schedulability_from_response_time_bound` uses the task-derived absolute
deadline (the accepted `job_deadline_from_task_deadline` instance), as the
elaborated source does. Binder orders follow the elaborated types. -/

section Task

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]
variable [JobArrival Job] [JobCost Job] [JobDeadline Job] [JobTask Job Task]
variable {PState : ProcessorState Job}
variable (arr_seq : arrival_sequence Job) (sched : schedule PState) (tsk : Task) (R : duration)

/-- Every arriving job of `tsk` completes within `R` time units of its arrival. -/
def task_response_time_bound : Prop :=
  ∀ j, arrives_in arr_seq j → job_of_task tsk j = true → job_response_time_bound sched j R = true

/-- Every arriving job of `tsk` meets its deadline. -/
def schedulable_task : Prop :=
  ∀ j, arrives_in arr_seq j → job_of_task tsk j = true → job_meets_deadline sched j = true

end Task

/-- A response-time bound no larger than the relative deadline implies
schedulability (absolute deadlines derived from the task deadline). -/
theorem schedulability_from_response_time_bound {Task : TaskType} [DecidableEq Task]
    [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]
    [JobTask Job Task] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (tsk : Task) (R : duration) :
    task_response_time_bound arr_seq sched tsk R → R ≤ task_deadline tsk →
      @schedulable_task Task _ Job _ _ (job_deadline_from_task_deadline Job Task) _ PState
        arr_seq sched tsk := by
  intro h hR j ha hj
  have hc := h j ha hj
  have htask : job_task (Task := Task) j = tsk := of_decide_eq_true hj
  unfold job_meets_deadline
  unfold job_response_time_bound at hc
  refine completion_monotonic sched j (job_arrival j + R) _ ?_ hc
  show job_arrival j + R ≤ job_arrival j + task_deadline (job_task (Task := Task) j)
  rw [htask]
  exact Nat.add_le_add_left hR _

section AllDeadlinesMet

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobDeadline Job]
variable {PState : ProcessorState Job}

/-- Every job scheduled at some point meets its deadline. -/
def all_deadlines_met (sched : schedule PState) : Prop :=
  ∀ j t, scheduled_at sched j t = true → job_meets_deadline sched j = true

/-- Every job of the arrival sequence meets its deadline. -/
def all_deadlines_of_arrivals_met (arr_seq : arrival_sequence Job) (sched : schedule PState) : Prop :=
  ∀ j, arrives_in arr_seq j → job_meets_deadline sched j = true

/-- If all jobs come from the arrival sequence and all its jobs meet their
deadlines, then all scheduled jobs meet their deadlines. -/
theorem all_deadlines_met_in_valid_schedule :
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState),
      jobs_come_from_arrival_sequence sched arr_seq →
      all_deadlines_of_arrivals_met arr_seq sched → all_deadlines_met sched :=
  fun _ _ hfrom hmet j t hs => hmet j (hfrom j t hs)

end AllDeadlinesMet

end Prosa.Analysis.Definitions.Schedulability
