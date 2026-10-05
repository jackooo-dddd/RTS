-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrival/request_bound_functions.v

import Prosa.Util.Rel
import Prosa.Model.Task.Arrivals

namespace Prosa.Model.Task.Arrival.RequestBoundFunctions

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals

/-! ## Task parameters for the request bound functions model -/

/-- `max_request_bound tsk Δ` bounds the cost of arrivals of `tsk` in any
interval of length `Δ`. -/
class MaxRequestBound (Task : TaskType) [DecidableEq Task] where
  max_request_bound : Task → duration → work

export MaxRequestBound (max_request_bound)

/-- `min_request_bound tsk Δ` lower-bounds the cost of arrivals of `tsk` in
any interval of length `Δ`. -/
class MinRequestBound (Task : TaskType) [DecidableEq Task] where
  min_request_bound : Task → duration → work

export MinRequestBound (min_request_bound)

/-! ## Parameter semantics -/

/-- A valid request bound function is zero on the empty interval and monotone. -/
def valid_request_bound_function (request_bound : duration → work) : Prop :=
  request_bound 0 = 0 ∧ Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) request_bound

/-- `max_request_bound (t2 - t1)` bounds the cost of `tsk`'s arrivals in `[t1, t2)`. -/
def respects_max_request_bound {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) (tsk : Task)
    (max_request_bound : duration → work) : Prop :=
  ∀ t1 t2 : instant, t1 ≤ t2 →
    cost_of_task_arrivals arr_seq tsk t1 t2 ≤ max_request_bound (t2 - t1)

/-- `min_request_bound (t2 - t1)` lower-bounds the cost of `tsk`'s arrivals in `[t1, t2)`. -/
def respects_min_request_bound {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) (tsk : Task)
    (min_request_bound : duration → work) : Prop :=
  ∀ t1 t2 : instant, t1 ≤ t2 →
    min_request_bound (t2 - t1) ≤ cost_of_task_arrivals arr_seq tsk t1 t2

/-! ## Model validity -/

/-- `request_bound` is a valid request bound function for every task of the set. -/
def valid_taskset_request_bound_function {Task : TaskType} [DecidableEq Task]
    (ts : TaskSet Task) (request_bound : Task → duration → work) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true →
    valid_request_bound_function (request_bound tsk)

/-- Every task of the task set respects its maximum request bound. -/
def taskset_respects_max_request_bound {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) [MaxRequestBound Task] (ts : TaskSet Task) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true →
    respects_max_request_bound arr_seq tsk (max_request_bound tsk)

/-- Every task of the task set respects its minimum request bound. -/
def taskset_respects_min_request_bound {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    (arr_seq : arrival_sequence Job) [MinRequestBound Task] (ts : TaskSet Task) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true →
    respects_min_request_bound arr_seq tsk (min_request_bound tsk)

end Prosa.Model.Task.Arrival.RequestBoundFunctions
