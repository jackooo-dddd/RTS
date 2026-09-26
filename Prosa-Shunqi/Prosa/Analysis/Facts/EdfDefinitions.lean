-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/edf_definitions.v

import Prosa.Analysis.Facts.Model.Ideal.Schedule
import Prosa.Analysis.Facts.Behavior.Deadlines
import Prosa.Analysis.Definitions.Schedulability
import Prosa.Model.Priority.Edf
import Prosa.Model.Schedule.Edf
import Prosa.Model.Schedule.PriorityDriven
import Prosa.Model.Readiness.Basic
import Prosa.Model.Preemption.FullyPreemptive

namespace Prosa.Analysis.Facts.EdfDefinitions

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Edf
open Prosa.Model.Schedule.Edf
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Readiness.Basic
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Deadlines
open Prosa.Analysis.Facts.Model.Ideal.Schedule

/-! Equivalence of the two EDF-schedule notions on the ideal uniprocessor.
Binders follow the elaborated source types (each lemma takes only the section
inputs and hypotheses it uses). As in the source's section, the basic
readiness model (`basic_ready_instance`: pending jobs are ready) and the fully
preemptive job model are enabled as local instances. Representation: a
Boolean in `Prop` position is `= true`. -/

section Equivalence

attribute [local instance] basic_ready_instance fully_preemptive_job_model

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobDeadline Job] [JobArrival Job]

theorem EDF_schedule_implies_respects_policy_at_preemption_point (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) :
    all_deadlines_of_arrivals_met arr_seq sched →
    EDF_schedule sched →
    respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job) := by
  intro H_no_deadline_misses EDF j' j t ARR _ BL SCHED
  obtain ⟨t', hrange, SCHED'⟩ := incomplete_implies_scheduled_later sched j' t
    (H_no_deadline_misses j' ARR) (backlogged_implies_incomplete sched j' t BL)
  have LE : t ≤ t' := of_decide_eq_true (Bool.and_eq_true_iff.mp hrange).1
  have ARRIVED := backlogged_implies_arrived sched j' t BL
  exact decide_eq_true (EDF t j SCHED t' j' LE SCHED' (of_decide_eq_true ARRIVED))

theorem respects_policy_at_preemption_point_implies_EDF_schedule (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      jobs_come_from_arrival_sequence sched arr_seq →
      respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job) →
      EDF_schedule sched := by
  intro _ sched _ H_completed H_from H_priority_driven t j_hp SCHED t' j LEQ SCHED' EARLIER_ARR
  by_cases EQ : j = j_hp
  · subst EQ; exact Nat.le_refl _
  · have NOT_SCHED : scheduled_at sched j t = false := by
      cases hs : scheduled_at sched j t with
      | false => rfl
      | true => exact absurd (ideal_proc_model_is_a_uniprocessor_model Job j j_hp sched t hs SCHED) EQ
    have INCOMPLETE : (!completed_by sched j t) = true :=
      incompletion_monotonic sched j t t' LEQ (scheduled_implies_not_completed sched j H_completed t' SCHED')
    have BACKLOGGED : backlogged sched j t = true := by
      show (pending sched j t && !scheduled_at sched j t) = true
      unfold pending
      rw [NOT_SCHED, INCOMPLETE]
      simp only [has_arrived, Bool.and_true, Bool.not_false]
      exact decide_eq_true EARLIER_ARR
    have PREEMPT : preemption_time arr_seq sched t = true := by
      unfold preemption_time
      cases scheduled_job_at arr_seq sched t <;> rfl
    have H := H_priority_driven j j_hp t (H_from j t' SCHED') PREEMPT BACKLOGGED SCHED
    exact of_decide_eq_true H

theorem EDF_schedule_equiv (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      jobs_must_arrive_to_execute sched → completed_jobs_dont_execute sched →
      jobs_come_from_arrival_sequence sched arr_seq → all_deadlines_of_arrivals_met arr_seq sched →
      (EDF_schedule sched ↔ respects_JLFP_policy_at_preemption_point arr_seq sched (EDF Job)) := by
  intro H_valid sched H_arrive H_completed H_from H_no_deadline_misses
  exact ⟨EDF_schedule_implies_respects_policy_at_preemption_point arr_seq sched H_no_deadline_misses,
    respects_policy_at_preemption_point_implies_EDF_schedule arr_seq H_valid sched H_arrive H_completed H_from⟩

end Equivalence

end Prosa.Analysis.Facts.EdfDefinitions
