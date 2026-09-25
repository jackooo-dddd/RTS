import Prosa.Implementation.Definitions.GenericScheduler

namespace Validation.GenericSchedulerLeanTypeAudit

open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Analysis.Transform.Swap
open Prosa.Implementation.Definitions.GenericScheduler

universe u v w

#check @PointwisePolicy
#check @empty_schedule
#check @schedule_up_to
#check @generic_schedule

example {Job : JobType} [DecidableEq Job]
    (PState : ProcessorState.{u, v, w} Job) :
    PointwisePolicy PState = (schedule PState → instant → PState.State) := rfl

example {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState.{u, v, w} Job}
    (idle_state : PState.State) :
    empty_schedule idle_state = (fun _ => idle_state) := rfl

example {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState.{u, v, w} Job}
    (policy : PointwisePolicy PState) (idle_state : PState.State) :
    schedule_up_to policy idle_state 0 =
      replace_at (empty_schedule idle_state) 0
        (policy (empty_schedule idle_state) 0) := rfl

example {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState.{u, v, w} Job}
    (policy : PointwisePolicy PState) (idle_state : PState.State)
    (h : instant) :
    schedule_up_to policy idle_state (h + 1) =
      replace_at (schedule_up_to policy idle_state h) (h + 1)
        (policy (schedule_up_to policy idle_state h) (h + 1)) := rfl

example {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState.{u, v, w} Job}
    (policy : PointwisePolicy PState) (idle_state : PState.State)
    (t : instant) :
    generic_schedule policy idle_state t =
      schedule_up_to policy idle_state t t := rfl

#print axioms PointwisePolicy
#print axioms empty_schedule
#print axioms schedule_up_to
#print axioms generic_schedule

end Validation.GenericSchedulerLeanTypeAudit
