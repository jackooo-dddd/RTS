-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/EDF/preemptive_sched.v

import Prosa.Analysis.Facts.Preemption.Task.Preemptive
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive
import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Analysis.Definitions.Tardiness
import Prosa.Implementation.Facts.IdealUni.PrioAware
import Prosa.Implementation.Definitions.Task
import Prosa.Model.Priority.Edf
import Prosa.Model.Task.AbsoluteDeadline

/-! # Fully-preemptive earliest-deadline-first schedules

The schedule is valid, and the EDF policy is respected at each preemption point.

Representation: the `Task`/`Job` aliases (the concrete types as `eqType`s) are abbreviations of the accepted
concrete types; `EDF Job` uses the source's global job-deadline instance (the accepted
`job_deadline_from_task_deadline`), passed explicitly; the source's `Instance basic_ready_instance` is a
global instance, as in the source, and the section-local
instances (this readiness model, `fully_preemptive_job_model` and `EDF` coerced to a JLDP policy) are passed
explicitly to `uni_schedule`; the section's `arr_seq` and `H_valid_arrivals` are explicit binders, in the order of
the elaborated types. -/

set_option linter.dupNamespace false
set_option warn.classDefReducibility false

namespace Prosa.Implementation.Refinements.EDF.PreemptiveSched

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Model.Processor.Ideal
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Priority.Edf
open Prosa.Model.Task.AbsoluteDeadline
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

/-- The basic readiness model. -/
noncomputable instance basic_ready_instance : JobReady Job (processor_state Job) :=
  Prosa.Model.Readiness.Basic.basic_ready_instance

/-- The fully-preemptive EDF schedule. -/
noncomputable def sched (arr_seq : arrival_sequence Job) : schedule (processor_state Job) :=
  @uni_schedule Job _ _ _ arr_seq basic_ready_instance fully_preemptive_job_model (JLFP_to_JLDP (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task)))

/-- The schedule is valid. -/
theorem sched_valid : ∀ arr_seq : arrival_sequence Job, valid_schedule (sched arr_seq) arr_seq :=
  fun arr_seq =>
    @uni_schedule_valid Job _ _ _ arr_seq basic_ready_instance
      Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_nonclairvoyance
      fully_preemptive_job_model (JLFP_to_JLDP (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task)))

/-- The EDF policy is respected at each preemption point. -/
theorem respects_policy_at_preemption_point_edf_fp :
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ _ fully_preemptive_job_model basic_ready_instance arr_seq
        (sched arr_seq) (@EDF Job _ (job_deadline_from_task_deadline Job Task)) :=
  fun arr_seq H_valid =>
    @schedule_respects_policy Job _ _ _ arr_seq H_valid basic_ready_instance
      Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_nonclairvoyance
      fully_preemptive_job_model (JLFP_to_JLDP (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task)))
      (reflexive_priorities_JLFP_implies_JLDP _ (@EDF_is_reflexive Job _ (job_deadline_from_task_deadline Job Task)))
      (total_priorities_JLFP_implies_JLDP _ (@EDF_is_total Job _ (job_deadline_from_task_deadline Job Task)))
      (transitive_priorities_JLFP_implies_JLDP _ (@EDF_is_transitive Job _ (job_deadline_from_task_deadline Job Task)))

end Prosa.Implementation.Refinements.EDF.PreemptiveSched
