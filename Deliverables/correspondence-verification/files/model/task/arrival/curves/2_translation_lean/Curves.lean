-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: model/task/arrival/curves.v

import Prosa.Util.Rel
import Prosa.Model.Task.Arrivals

namespace Prosa.Model.Task.Arrival.Curves

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals

/-! ## Task parameters for the arrival curves model -/

/-- `max_arrivals tsk Δ` bounds the number of arrivals of `tsk` in any
interval of length `Δ`. -/
class MaxArrivals (Task : TaskType) [DecidableEq Task] where
  max_arrivals : Task → duration → Nat

export MaxArrivals (max_arrivals)

/-- `min_arrivals tsk Δ` lower-bounds the number of arrivals of `tsk` in any
interval of length `Δ`. -/
class MinArrivals (Task : TaskType) [DecidableEq Task] where
  min_arrivals : Task → duration → Nat

export MinArrivals (min_arrivals)

/-- `min_separation tsk N` is the minimal length of an interval in which
exactly `N` jobs of `tsk` arrive. -/
class MinSeparation (Task : TaskType) [DecidableEq Task] where
  min_separation : Task → Nat → duration

export MinSeparation (min_separation)

/-- `max_separation tsk N` is the maximal length of an interval in which
exactly `N` jobs of `tsk` arrive. -/
class MaxSeparation (Task : TaskType) [DecidableEq Task] where
  max_separation : Task → Nat → duration

export MaxSeparation (max_separation)

/-! ## Parameter semantics -/

/-- A valid arrival curve is zero on the empty interval and monotone. -/
def valid_arrival_curve (num_arrivals : duration → Nat) : Prop :=
  num_arrivals 0 = 0 ∧ Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) num_arrivals

/-- `max_arrivals (t2 - t1)` bounds the arrivals of `tsk` in `[t1, t2)`. -/
def respects_max_arrivals {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) (tsk : Task)
    (max_arrivals : duration → Nat) : Prop :=
  ∀ t1 t2 : instant, t1 ≤ t2 →
    number_of_task_arrivals arr_seq tsk t1 t2 ≤ max_arrivals (t2 - t1)

/-- `min_arrivals (t2 - t1)` lower-bounds the arrivals of `tsk` in `[t1, t2)`. -/
def respects_min_arrivals {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) (tsk : Task)
    (min_arrivals : duration → Nat) : Prop :=
  ∀ t1 t2 : instant, t1 ≤ t2 →
    min_arrivals (t2 - t1) ≤ number_of_task_arrivals arr_seq tsk t1 t2

/-- `min_separation` lower-bounds the interval length for a number of arrivals. -/
def respects_min_separation {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) (tsk : Task)
    (min_separation : Nat → duration) : Prop :=
  ∀ t1 t2 : instant, t1 ≤ t2 →
    min_separation (number_of_task_arrivals arr_seq tsk t1 t2) ≤ t2 - t1

/-- `max_separation` upper-bounds the interval length for a number of arrivals. -/
def respects_max_separation {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) (tsk : Task)
    (max_separation : Nat → duration) : Prop :=
  ∀ t1 t2 : instant, t1 ≤ t2 →
    t2 - t1 ≤ max_separation (number_of_task_arrivals arr_seq tsk t1 t2)

/-! ## Model validity -/

/-- `arrivals` is a valid arrival curve for every task of the task set. -/
def valid_taskset_arrival_curve {Task : TaskType} [DecidableEq Task]
    (ts : TaskSet Task) (arrivals : Task → duration → Nat) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true → valid_arrival_curve (arrivals tsk)

/-- Every task of the task set respects its maximum arrival curve. -/
def taskset_respects_max_arrivals {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) [MaxArrivals Task] (ts : TaskSet Task) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true →
    respects_max_arrivals arr_seq tsk (max_arrivals tsk)

/-- Every task of the task set respects its minimum arrival curve. -/
def taskset_respects_min_arrivals {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) [MinArrivals Task] (ts : TaskSet Task) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true →
    respects_min_arrivals arr_seq tsk (min_arrivals tsk)

/-- Every task of the task set respects its maximum separation bound. -/
def taskset_respects_max_separation {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) [MaxSeparation Task] (ts : TaskSet Task) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true →
    respects_max_separation arr_seq tsk (max_separation tsk)

/-- Every task of the task set respects its minimum separation bound. -/
def taskset_respects_min_separation {Task : TaskType} [DecidableEq Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) [MinSeparation Task] (ts : TaskSet Task) : Prop :=
  ∀ tsk : Task, decide (tsk ∈ ts) = true →
    respects_min_separation arr_seq tsk (min_separation tsk)

end Prosa.Model.Task.Arrival.Curves
