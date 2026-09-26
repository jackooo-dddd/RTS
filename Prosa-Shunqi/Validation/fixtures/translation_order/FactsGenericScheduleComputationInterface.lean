import Prosa.Implementation.Facts.GenericSchedule
import Validation.fixtures.translation_order.FactsReplaceAtComputationInterface

/-!
Export root for `implementation/facts/generic_schedule.v`: the six statements
together with the accepted replace-at export root (Service / Schedule closure
with the kernel-checked `replace_at` case equations), the generic scheduler,
and kernel-checked equations for the structurally recursive `schedule_up_to`
and for `empty_schedule`.  Every equation is proved in Lean and exported with
its proof.
-/

namespace Prosa.Validation.GenericScheduleInterface

open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Analysis.Transform.Swap
open Prosa.Implementation.Definitions.GenericScheduler

universe u v w

variable {Job : Prosa.Behavior.Job.JobType} [DecidableEq Job] {PState : ProcessorState.{u, v, w} Job}

theorem production_schedule_up_to_zero (policy : PointwisePolicy PState) (idle_state : PState.State) :
    schedule_up_to policy idle_state 0 =
      replace_at (empty_schedule idle_state) 0 (policy (empty_schedule idle_state) 0) := rfl

theorem production_schedule_up_to_succ (policy : PointwisePolicy PState) (idle_state : PState.State)
    (h : Nat) :
    schedule_up_to policy idle_state (h + 1) =
      replace_at (schedule_up_to policy idle_state h) (h + 1)
        (policy (schedule_up_to policy idle_state h) (h + 1)) := rfl

theorem production_empty_schedule (idle_state : PState.State) (t : instant) :
    empty_schedule idle_state t = idle_state := rfl

end Prosa.Validation.GenericScheduleInterface
