import Prosa.Implementation.Definitions.Task
import Validation.fixtures.translation_order.IdealUniSchedulerComputationInterface
import Validation.fixtures.translation_order.ExtrapolatedArrivalCurveArithmeticInterface

/-!
Shared export interface for `implementation/refinements/{EDF,FP}/{preemptive,nonpreemptive}_sched.v`.

The statements of these files are over the concrete job type, so the scheduler, arrival-sequence and list
definitions they mention are the concrete (universe-0) copies, which the generic interface equations do not
mention.  The equations below are the accepted `BigcatInterface` and `IdealUniSchedulerInterface` equations,
instantiated at the concrete job type; each is proved by the accepted generic one.  No new equation is added.
-/

namespace Prosa.Validation.RefSchedInterface

open Prosa.Util.Notation
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Analysis.Transform.Swap
open Prosa.Implementation.Definitions.GenericScheduler
open Prosa.Implementation.Definitions.Task

theorem production_bigCat_job_same (m : Nat) (f : Nat → List concrete_job) :
    bigCat m m f = [] :=
  Prosa.Validation.BigcatInterface.production_bigCat_same m f

theorem production_bigCat_job_of_le (m n : Nat) (f : Nat → List concrete_job) (h : n ≤ m) :
    bigCat m n f = [] :=
  Prosa.Validation.BigcatInterface.production_bigCat_of_le m n f h

theorem production_bigCat_job_add_succ (m d : Nat) (f : Nat → List concrete_job) :
    bigCat m (m + (d + 1)) f = bigCat m (m + d) f ++ f (m + d) :=
  Prosa.Validation.BigcatInterface.production_bigCat_add_succ m d f

theorem production_filter_job_nil (p : concrete_job → Bool) :
    List.filter p [] = [] :=
  Prosa.Validation.BigcatInterface.production_filter_nil p

theorem production_filter_job_cons (p : concrete_job → Bool) (x : concrete_job) (xs : List concrete_job) :
    List.filter p (x :: xs) = match p x with
      | true => x :: List.filter p xs
      | false => List.filter p xs :=
  Prosa.Validation.BigcatInterface.production_filter_cons p x xs

theorem production_schedule_up_to_job_zero (policy : PointwisePolicy (processor_state concrete_job))
    (idle_state : (processor_state concrete_job).State) :
    schedule_up_to policy idle_state 0 =
      replace_at (empty_schedule idle_state) 0 (policy (empty_schedule idle_state) 0) :=
  Prosa.Validation.IdealUniSchedulerInterface.production_schedule_up_to_zero policy idle_state

theorem production_schedule_up_to_job_succ (policy : PointwisePolicy (processor_state concrete_job))
    (idle_state : (processor_state concrete_job).State) (h : Nat) :
    schedule_up_to policy idle_state (h + 1) =
      replace_at (schedule_up_to policy idle_state h) (h + 1)
        (policy (schedule_up_to policy idle_state h) (h + 1)) :=
  Prosa.Validation.IdealUniSchedulerInterface.production_schedule_up_to_succ policy idle_state h

theorem production_empty_schedule_job (idle_state : (processor_state concrete_job).State) (t : instant) :
    empty_schedule (PState := processor_state concrete_job) idle_state t = idle_state :=
  Prosa.Validation.IdealUniSchedulerInterface.production_empty_schedule idle_state t

theorem production_replace_at_job_same (sched : schedule (processor_state concrete_job)) (t' : instant)
    (ns : (processor_state concrete_job).State) (t : instant) (h : t = t') :
    replace_at sched t' ns t = ns :=
  Prosa.Validation.IdealUniSchedulerInterface.production_replace_at_same sched t' ns t h

theorem production_replace_at_job_other (sched : schedule (processor_state concrete_job)) (t' : instant)
    (ns : (processor_state concrete_job).State) (t : instant) (h : ¬ t = t') :
    replace_at sched t' ns t = sched t :=
  Prosa.Validation.IdealUniSchedulerInterface.production_replace_at_other sched t' ns t h

theorem production_ideal_scheduled_in_job (j : concrete_job) (s : (processor_state concrete_job).State) :
    ProcessorState.scheduled_in (processor_state concrete_job) j s =
      (processor_state concrete_job).scheduled_on j s () :=
  Prosa.Validation.IdealUniSchedulerInterface.production_ideal_scheduled_in j s

theorem production_ideal_service_in_job (j : concrete_job) (s : (processor_state concrete_job).State) :
    ProcessorState.service_in (processor_state concrete_job) j s =
      (processor_state concrete_job).service_on j s () :=
  Prosa.Validation.IdealUniSchedulerInterface.production_ideal_service_in j s

#print axioms production_bigCat_job_same
#print axioms production_bigCat_job_of_le
#print axioms production_bigCat_job_add_succ
#print axioms production_filter_job_nil
#print axioms production_filter_job_cons
#print axioms production_schedule_up_to_job_zero
#print axioms production_schedule_up_to_job_succ
#print axioms production_empty_schedule_job
#print axioms production_replace_at_job_same
#print axioms production_replace_at_job_other
#print axioms production_ideal_scheduled_in_job
#print axioms production_ideal_service_in_job

end Prosa.Validation.RefSchedInterface
