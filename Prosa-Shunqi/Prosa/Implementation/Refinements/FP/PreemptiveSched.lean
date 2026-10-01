-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/FP/preemptive_sched.v

import Prosa.Analysis.Facts.Preemption.Task.Preemptive
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive
import Prosa.Analysis.Facts.Readiness.Sequential
import Prosa.Analysis.Definitions.Tardiness
import Prosa.Implementation.Facts.IdealUni.PrioAware
import Prosa.Implementation.Definitions.Task

/-! # Fully-preemptive fixed-priority schedules

The schedule is valid, and the fixed-priority policy is respected at each preemption point.

Representation: the `Task`/`Job` aliases (the concrete types as `eqType`s) are abbreviations of the accepted
concrete types; the source's section `Instance sequential_ready_instance` (which depends on `arr_seq`) is a
definition taking `arr_seq`, passed explicitly wherever the elaborated types use it, as are the section-local
instances `fully_preemptive_job_model` and `NumericFPAscending` (through the accepted canonical FP → JLFP → JLDP
conversions); the section's `arr_seq` and `H_valid_arrivals` are explicit binders, in the order of the elaborated
types. -/

set_option linter.dupNamespace false
set_option warn.classDefReducibility false

namespace Prosa.Implementation.Refinements.FP.PreemptiveSched

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Model.Processor.Ideal
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Priority.NumericFixedPriority
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Analysis.Definitions.Readiness
open Prosa.Implementation.Definitions.Task
open Prosa.Implementation.Definitions.IdealUniScheduler
open Prosa.Implementation.Facts.IdealUni.PrioAware

/-- The concrete task type. -/
abbrev Task : Type := concrete_task

/-- The concrete job type. -/
abbrev Job : Type := concrete_job

/-- The sequential readiness model of an arrival sequence. -/
noncomputable def sequential_ready_instance (arr_seq : arrival_sequence Job) : JobReady Job (processor_state Job) :=
  Prosa.Model.Readiness.Sequential.sequential_ready_instance (Task := Task) arr_seq

/-- The fully-preemptive fixed-priority schedule. -/
noncomputable def sched (arr_seq : arrival_sequence Job) : schedule (processor_state Job) :=
  @uni_schedule Job _ _ _ arr_seq (sequential_ready_instance arr_seq) fully_preemptive_job_model
    (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) (NumericFPAscending Task)))

/-- The schedule is valid. -/
theorem sched_valid :
    ∀ arr_seq : arrival_sequence Job,
      @valid_schedule Job _ _ _ (sched arr_seq) _ (sequential_ready_instance arr_seq) arr_seq :=
  fun arr_seq =>
    @uni_schedule_valid Job _ _ _ arr_seq (sequential_ready_instance arr_seq)
      (Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_nonclairvoyance (Task := Task) arr_seq)
      fully_preemptive_job_model (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) (NumericFPAscending Task)))

/-- The fixed-priority policy is respected at each preemption point. -/
theorem respects_policy_at_preemption_point :
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ _ fully_preemptive_job_model
        (sequential_ready_instance arr_seq) arr_seq (sched arr_seq) (NumericFPAscending Task) :=
  fun arr_seq H_valid =>
    @schedule_respects_policy Job _ _ _ arr_seq H_valid (sequential_ready_instance arr_seq)
      (Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_nonclairvoyance (Task := Task) arr_seq)
      fully_preemptive_job_model (JLFP_to_JLDP (JLFP := FP_to_JLFP (Task := Task) (NumericFPAscending Task)))
      (reflexive_priorities_JLFP_implies_JLDP _
        (reflexive_priorities_FP_implies_JLFP (Job := Job) _ NFPA_is_reflexive))
      (total_priorities_JLFP_implies_JLDP _ (total_priorities_FP_implies_JLFP (Job := Job) _ NFPA_is_total))
      (transitive_priorities_JLFP_implies_JLDP _
        (transitive_priorities_FP_implies_JLFP (Job := Job) _ NFPA_is_transitive))

end Prosa.Implementation.Refinements.FP.PreemptiveSched
