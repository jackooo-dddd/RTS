-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/optimality/edf.v

import Prosa.Model.Readiness.Basic
import Prosa.Model.Preemption.FullyPreemptive
import Prosa.Analysis.Facts.Transform.EdfOpt
import Prosa.Analysis.Facts.Transform.EdfWc
import Prosa.Analysis.Facts.EdfDefinitions
import Prosa.Model.Priority.Edf

namespace Prosa.Results.Optimality.Edf

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Readiness.Basic
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Model.Priority.Edf
open Prosa.Model.Schedule.Edf
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Schedule.WorkConserving
open Prosa.Analysis.Transform.EdfTrans
open Prosa.Analysis.Transform.WcTrans
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Facts.Transform.EdfOpt
open Prosa.Analysis.Facts.Transform.WcCorrectness
open Prosa.Analysis.Facts.Transform.EdfWc
open Prosa.Analysis.Facts.EdfDefinitions
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion

/-! Optimality of EDF on ideal uniprocessors.

Binder orders and hypothesis sets follow the elaborated source types (the valid-arrival-sequence hypothesis is
present only where the elaborated type has it). The processor model is the accepted ideal processor
`processor_state Job`; the sections' local `basic_ready_instance` and `fully_preemptive_job_model` are the accepted
Lean definitions, registered as local instances, so readiness and preemptability in the statements are those
instances, as in the elaborated types. A Boolean in `Prop` position is `= true`. -/

section Optimality

variable {Job : JobType} [DecidableEq Job]

attribute [local instance] basic_ready_instance fully_preemptive_job_model

/-- If some valid schedule meets all deadlines of the arrival sequence, then so does an EDF schedule. -/
theorem EDF_optimality [JobCost Job] [JobDeadline Job] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    (∃ any_sched : schedule (processor_state Job),
        valid_schedule any_sched arr_seq ∧ all_deadlines_of_arrivals_met arr_seq any_sched) →
      ∃ edf_sched : schedule (processor_state Job),
        valid_schedule edf_sched arr_seq ∧ all_deadlines_of_arrivals_met arr_seq edf_sched ∧
          EDF_schedule edf_sched := by
  intro ⟨sched, hvs, hdoa⟩
  have hmust := jobs_must_arrive_to_be_ready sched hvs.2
  have hcde := completed_jobs_are_not_ready sched hvs.2
  have hdm := all_deadlines_met_in_valid_schedule arr_seq sched hvs.1 hdoa
  exact ⟨edf_transform sched, edf_schedule_is_valid arr_seq sched hvs hdm,
    edf_schedule_meets_all_deadlines_wrt_arrivals arr_seq sched hvs hdoa,
    edf_transform_ensures_edf sched hmust hcde hdm⟩

/-- If some valid schedule meets all deadlines of the arrival sequence, then so does a work-conserving EDF
schedule. -/
theorem EDF_WC_optimality [JobCost Job] [JobDeadline Job] [JobArrival Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      (∃ any_sched : schedule (processor_state Job),
          valid_schedule any_sched arr_seq ∧ all_deadlines_of_arrivals_met arr_seq any_sched) →
        ∃ edf_wc_sched : schedule (processor_state Job),
          valid_schedule edf_wc_sched arr_seq ∧ all_deadlines_of_arrivals_met arr_seq edf_wc_sched ∧
            work_conserving arr_seq edf_wc_sched ∧ EDF_schedule edf_wc_sched := by
  intro hva ⟨sched, hvs, hdoa⟩
  have hwvs : valid_schedule (wc_transform arr_seq sched) arr_seq :=
    ⟨wc_jobs_come_from_arrival_sequence arr_seq sched hvs, wc_jobs_must_be_ready_to_execute arr_seq sched hvs⟩
  have hwdoa := wc_all_deadlines_of_arrivals_met arr_seq sched hdoa
  have hwmust := jobs_must_arrive_to_be_ready (wc_transform arr_seq sched) hwvs.2
  have hwcde := completed_jobs_are_not_ready (wc_transform arr_seq sched) hwvs.2
  have hwdm := all_deadlines_met_in_valid_schedule arr_seq _ hwvs.1 hwdoa
  exact ⟨edf_transform (wc_transform arr_seq sched), edf_schedule_is_valid arr_seq _ hwvs hwdm,
    edf_schedule_meets_all_deadlines_wrt_arrivals arr_seq _ hwvs hwdoa,
    edf_transform_maintains_work_conservation arr_seq _ hwvs hwdm (wc_is_work_conserving arr_seq hva sched hdoa),
    edf_transform_ensures_edf _ hwmust hwcde hwdm⟩

/-- If some valid schedule meets all deadlines of the arrival sequence, then so does a work-conserving schedule
that respects the EDF policy at every preemption point. -/
theorem EDF_priority_compliant_WC_optimality [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
      (∃ any_sched : schedule (processor_state Job),
          valid_schedule any_sched arr_seq ∧ all_deadlines_of_arrivals_met arr_seq any_sched) →
        ∃ priority_compliant_sched : schedule (processor_state Job),
          valid_schedule priority_compliant_sched arr_seq ∧
            all_deadlines_of_arrivals_met arr_seq priority_compliant_sched ∧
              work_conserving arr_seq priority_compliant_sched ∧
                respects_JLFP_policy_at_preemption_point arr_seq priority_compliant_sched (EDF Job) := by
  intro hva hex
  obtain ⟨edf_sched, hvs, hdoa, hwc, hedf⟩ := EDF_WC_optimality arr_seq hva hex
  refine ⟨edf_sched, hvs, hdoa, hwc, ?_⟩
  exact (EDF_schedule_equiv arr_seq hva edf_sched (jobs_must_arrive_to_be_ready edf_sched hvs.2)
    (completed_jobs_are_not_ready edf_sched hvs.2) hvs.1 hdoa).1 hedf

end Optimality

section WeakOptimality

variable {Job : JobType} [DecidableEq Job]

/-- A schedule without deadline misses yields an EDF schedule of the same jobs without deadline misses. -/
theorem weak_EDF_optimality [JobCost Job] [JobDeadline Job] [JobArrival Job]
    (any_sched : schedule (processor_state Job)) :
    jobs_must_arrive_to_execute any_sched → completed_jobs_dont_execute any_sched → all_deadlines_met any_sched →
      ∃ edf_sched : schedule (processor_state Job),
        jobs_must_arrive_to_execute edf_sched ∧ completed_jobs_dont_execute edf_sched ∧
          all_deadlines_met edf_sched ∧ EDF_schedule edf_sched ∧
            ∀ j : Job, (∃ t : instant, scheduled_at any_sched j t = true) ↔
              (∃ t' : instant, scheduled_at edf_sched j t' = true) := by
  intro hmust hcde hdm
  refine ⟨edf_transform any_sched, edf_transform_jobs_must_arrive any_sched hmust hcde hdm,
    edf_transform_completed_jobs_dont_execute any_sched hmust hcde hdm,
    edf_transform_deadlines_met any_sched hmust hcde hdm, edf_transform_ensures_edf any_sched hmust hcde hdm,
    fun j => ⟨fun ⟨t, ht⟩ => edf_transform_job_scheduled' any_sched hmust hcde hdm j t ht,
      fun ⟨t, ht⟩ => edf_transform_job_scheduled any_sched j t ht⟩⟩

end WeakOptimality

end Prosa.Results.Optimality.Edf
