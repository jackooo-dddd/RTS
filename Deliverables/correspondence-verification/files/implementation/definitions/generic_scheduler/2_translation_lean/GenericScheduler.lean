-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/definitions/generic_scheduler.v

import Prosa.Analysis.Transform.Swap

namespace Prosa.Implementation.Definitions.GenericScheduler

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Analysis.Transform.Swap

universe u v w

/-- A decision for the current instant based on the schedule prefix. -/
def PointwisePolicy {Job : JobType} [DecidableEq Job]
    (PState : ProcessorState.{u, v, w} Job) : Type _ :=
  schedule PState → instant → PState.State

section GenericSchedule

variable {Job : JobType} [DecidableEq Job]
variable {PState : ProcessorState.{u, v, w} Job}

/-- The all-idle base schedule. -/
def empty_schedule (idle_state : PState.State) : schedule PState :=
  fun _ => idle_state

/-- Build a finite prefix through the current instant. -/
def schedule_up_to (policy : PointwisePolicy PState)
    (idle_state : PState.State) : instant → schedule PState
  | 0 =>
      let sched_prefix := empty_schedule idle_state
      replace_at sched_prefix 0 (policy sched_prefix 0)
  | h + 1 =>
      let sched_prefix := schedule_up_to policy idle_state h
      replace_at sched_prefix (h + 1) (policy sched_prefix (h + 1))

/-- Observe the state selected by the prefix built through `t`. -/
def generic_schedule (policy : PointwisePolicy PState)
    (idle_state : PState.State) (t : instant) : PState.State :=
  schedule_up_to policy idle_state t t

end GenericSchedule

end Prosa.Implementation.Definitions.GenericScheduler
