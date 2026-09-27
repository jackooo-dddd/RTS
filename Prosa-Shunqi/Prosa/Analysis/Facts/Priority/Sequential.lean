-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/priority/sequential.v

import Prosa.Analysis.Definitions.AlwaysHigherPriority
import Prosa.Analysis.Definitions.WorkBearingReadiness
import Prosa.Analysis.Facts.Model.Preemption

namespace Prosa.Analysis.Facts.Priority.Sequential

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.AlwaysHigherPriority
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Preemption

/-! If `j1` arrives before `j2` and always has higher priority, `j2` is
scheduled only after `j1` completes.
Binders follow the elaborated source type (the JLFP policy, processor model,
readiness and preemption model are quantified at their elaborated positions;
`always_higher_priority` uses the JLFP policy through the canonical JLDP
coercion). Representation: a Boolean in `Prop` position is `= true`. -/

section SequentialJLFP

variable {Job : JobType} [DecidableEq Job] [JobArrival Job] [JobCost Job]

theorem early_hep_job_is_scheduled (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ JLFP : JLFP_policy Job, transitive_job_priorities JLFP →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ (sched : schedule PState) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j1 j2 : Job, arrives_in arr_seq j1 → job_arrival j1 < job_arrival j2 →
      always_higher_priority j1 j2 →
    ∀ t : instant, scheduled_at sched j2 t = true → completed_by sched j1 t = true := by
  intro hva JLFP htrans PState huni sched _ hwb hvs _ hvpm hresp j1 j2 ha1 hlt hahp t hs
  cases hc : completed_by sched j1 t
  · exfalso
    obtain ⟨pt, hin, hpt, hall⟩ :=
      scheduling_of_any_segment_starts_with_preemption_time huni arr_seq hva sched hvs hvpm j2 t hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    have hs2 : scheduled_at sched j2 pt = true :=
      hall pt (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    have hncpt : completed_by sched j1 pt = false := by
      cases hcp : completed_by sched j1 pt
      · rfl
      · have := completion_monotonic sched j1 pt t hin.2 hcp
        rw [hc] at this; exact absurd this (by decide)
    have hpend : pending sched j1 pt = true := by
      unfold pending has_arrived
      rw [hncpt]
      simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
      omega'
    obtain ⟨j3, ha3, hr3, hep3⟩ := hwb j1 pt ha1 hpend
    have hahpt := hahp pt
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hahpt
    have hnhep : JLFP.hep_job j2 j1 = false := hahpt.2
    have hback : backlogged sched j3 pt = true := by
      unfold backlogged
      rw [hr3]
      cases hs3 : scheduled_at sched j3 pt
      · rfl
      · have heq : j2 = j3 := huni j2 j3 sched pt hs2 hs3
        rw [← heq] at hep3
        rw [hep3] at hnhep
        exact absurd hnhep (by decide)
    have hep23 : JLFP.hep_job j2 j3 = true :=
      hresp j3 j2 pt ha3 hpt hback hs2
    have := htrans j3 j2 j1 hep23 hep3
    rw [this] at hnhep
    exact absurd hnhep (by decide)
  · rfl

end SequentialJLFP

end Prosa.Analysis.Facts.Priority.Sequential
