import Prosa.Implementation.Definitions.IdealUniScheduler
import Validation.fixtures.translation_order.TransformPrefixComputationInterface

/-!
Export root for `implementation/definitions/ideal_uni_scheduler.v`: the five
definitions together with the accepted transform-prefix export root
(preemption-parameter closure with the Service / Schedule interfaces), the
ideal processor, the generic scheduler, the work-conserving backlog, and
kernel-checked equations, at the ideal processor, for the structurally
recursive `schedule_up_to`, for `empty_schedule` and for `replace_at`.  Every
equation is proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.IdealUniSchedulerInterface

open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Transform.Swap
open Prosa.Implementation.Definitions.GenericScheduler

variable {Job : Prosa.Behavior.Job.JobType} [DecidableEq Job]

theorem production_schedule_up_to_zero (policy : PointwisePolicy (processor_state Job))
    (idle_state : (processor_state Job).State) :
    schedule_up_to policy idle_state 0 =
      replace_at (empty_schedule idle_state) 0 (policy (empty_schedule idle_state) 0) := rfl

theorem production_schedule_up_to_succ (policy : PointwisePolicy (processor_state Job))
    (idle_state : (processor_state Job).State) (h : Nat) :
    schedule_up_to policy idle_state (h + 1) =
      replace_at (schedule_up_to policy idle_state h) (h + 1)
        (policy (schedule_up_to policy idle_state h) (h + 1)) := rfl

theorem production_empty_schedule (idle_state : (processor_state Job).State) (t : instant) :
    empty_schedule (PState := processor_state Job) idle_state t = idle_state := rfl

theorem production_replace_at_same (sched : schedule (processor_state Job)) (t' : instant)
    (ns : (processor_state Job).State) (t : instant) (h : t = t') :
    replace_at sched t' ns t = ns := by
  subst h; simp [replace_at]

theorem production_replace_at_other (sched : schedule (processor_state Job)) (t' : instant)
    (ns : (processor_state Job).State) (t : instant) (h : ¬ t = t') :
    replace_at sched t' ns t = sched t := by
  simp only [replace_at]
  rw [if_neg]
  intro e
  exact h (beq_iff_eq.mp e).symm

theorem production_ideal_scheduled_in (j : Job) (s : (processor_state Job).State) :
    ProcessorState.scheduled_in (processor_state Job) j s =
      (processor_state Job).scheduled_on j s () := by
  change (Finset.univ : Finset Unit).fold Bool.or false
      (fun _ => (processor_state Job).scheduled_on j s ()) = _
  cases (processor_state Job).scheduled_on j s () <;> rfl

theorem production_ideal_service_in (j : Job) (s : (processor_state Job).State) :
    ProcessorState.service_in (processor_state Job) j s =
      (processor_state Job).service_on j s () := rfl

end Prosa.Validation.IdealUniSchedulerInterface
