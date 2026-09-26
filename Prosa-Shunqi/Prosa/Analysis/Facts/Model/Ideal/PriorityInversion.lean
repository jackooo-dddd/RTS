-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/ideal/priority_inversion.v

import Prosa.Analysis.Facts.Priority.Inversion
import Prosa.Analysis.Facts.Model.Ideal.Schedule

namespace Prosa.Analysis.Facts.Model.Ideal.PriorityInversion

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Facts.Priority.Inversion
open Prosa.Analysis.Facts.Model.Ideal.Schedule

/-! Priority inversion on the ideal uniprocessor. Binders follow the
elaborated source types: each lemma takes only the section inputs and
hypotheses it uses (the unused task, cost and completion context is absent),
and the JLFP policy, quantified after the schedule hypotheses, is a `∀ [..]`
binder. Representation: a Boolean in `Prop` position is `= true`; `~~ b` is
`!b`. -/

section PIIdealProcessorModelLemmas

variable {Job : JobType} [DecidableEq Job] [JobArrival Job]

theorem idle_implies_no_priority_inversion (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ [JLFP : JLFP_policy Job] (j : Job) (t : instant),
        ideal_is_idle sched t = true → (!priority_inversion arr_seq sched j t) = true := by
  intro H_valid sched H_from H_arrive _ j t IDLE
  apply no_priority_inversion_when_idle arr_seq H_valid sched H_from H_arrive j t
  rw [is_idle_def Job arr_seq sched H_from H_arrive H_valid t]
  exact IDLE

theorem priority_inversion_equiv_sched_lower_priority (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
      ∀ (j : Job) (t : instant) (j' : Job),
        scheduled_at sched j' t = true → priority_inversion arr_seq sched j t = !hep_job j' j := by
  intro H_valid sched H_from H_arrive JLFP H_refl j t j' SCHED
  exact priority_inversion_hep_job arr_seq H_valid sched H_from H_arrive H_refl j
    (ideal_proc_model_is_a_uniprocessor_model Job) t j' SCHED

theorem sched_hep_implies_no_priority_inversion (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
      ∀ (j : Job) (t : instant) (j' : Job),
        scheduled_at sched j' t = true → hep_job j' j = true →
          priority_inversion arr_seq sched j t = false := by
  intro H_valid sched H_from H_arrive JLFP H_refl j t j' SCHED HEP
  rw [priority_inversion_equiv_sched_lower_priority arr_seq H_valid sched H_from H_arrive H_refl j t j' SCHED,
    HEP]
  rfl

theorem sched_lp_implies_priority_inversion (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule (processor_state Job),
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
      ∀ [JLFP : JLFP_policy Job], reflexive_job_priorities JLFP →
      ∀ (j : Job) (t : instant) (j' : Job),
        scheduled_at sched j' t = true → (!hep_job j' j) = true →
          priority_inversion arr_seq sched j t = true := by
  intro H_valid sched H_from H_arrive JLFP H_refl j t j' SCHED NHEP
  rw [priority_inversion_equiv_sched_lower_priority arr_seq H_valid sched H_from H_arrive H_refl j t j' SCHED]
  exact NHEP

end PIIdealProcessorModelLemmas

end Prosa.Analysis.Facts.Model.Ideal.PriorityInversion
