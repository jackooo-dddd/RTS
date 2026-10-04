-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/busy_interval/hep_at_pt.v

import Prosa.Model.Schedule.PriorityDriven
import Prosa.Analysis.Facts.BusyInterval.Existence
import Prosa.Util.Tactics
import Prosa.Model.Task.Preemption.Parameters
import Prosa.Analysis.Facts.Model.Preemption

namespace Prosa.Analysis.Facts.BusyInterval.HepAtPt

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Schedule.WorkConserving
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.Preemption
open Prosa.Analysis.Facts.BusyInterval.Existence

/-! The processor is busy with higher-or-equal-priority jobs at (and after)
preemption points inside a busy-interval prefix.
Binders follow the elaborated source types: every lemma takes only the section
inputs and hypotheses it uses, in their elaborated order; instance inputs
quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `~ P` is `¬ P`;
`a <= b < c` is a Boolean conjunction of decides; `t.+1` is `t + 1`;
`t.-1` is `t - 1`. -/

section HepAtPt

variable {Job : JobType} [DecidableEq Job]

/-- A higher-or-equal-priority job that is pending at `t` but not scheduled
yields, at a preemption time, a contradiction with a lower-priority scheduled
job. -/
private theorem hep_of_pending_hep [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (huni : uniprocessor_model PState) (sched : schedule PState) (JLFP : JLFP_policy Job)
    (htrans : transitive_job_priorities JLFP) [JobPreemptable Job] [JobReady Job PState]
    (hwb : work_bearing_readiness arr_seq sched)
    (hresp : respects_JLFP_policy_at_preemption_point arr_seq sched JLFP)
    (j : Job) (t : instant) (hpt : preemption_time arr_seq sched t = true)
    (j_hp : Job) (ha : arrives_in arr_seq j_hp) (hhp : JLFP.hep_job j_hp j = true)
    (hpend : pending sched j_hp t = true)
    (jlp : Job) (hs : scheduled_at sched jlp t = true) : JLFP.hep_job jlp j = true := by
  obtain ⟨j', ha', hr', hhep'⟩ := hwb j_hp t ha hpend
  have hhep : JLFP.hep_job j' j = true := htrans j_hp j' j hhep' hhp
  cases hs' : scheduled_at sched j' t
  · have hback : backlogged sched j' t = true := by
      unfold backlogged
      rw [hr', hs']
      rfl
    have hpp : JLFP.hep_job jlp j' = true := hresp j' jlp t ha' hpt hback hs
    exact htrans j' jlp j hpp hhep
  · have := huni jlp j' sched t hs hs'
    subst this
    exact hhep

/-- Inside a busy-interval prefix the processor is not idle. -/
theorem instant_t_is_not_idle [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job} (sched : schedule PState) (JLFP : JLFP_policy Job),
      reflexive_job_priorities JLFP →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched → valid_schedule sched arr_seq →
      work_conserving arr_seq sched →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true →
      ¬ is_idle arr_seq sched t = true := by
  intro hva PState sched JLFP hrefl _ hwb hvs hwc j ha hpos t1 t2 hbip t ht
  exact not_quiet_implies_not_idle arr_seq hva sched hvs.1
    (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) JLFP hwb j ha hpos hwc hrefl
    t1 t2 hbip t ht

/-- At a preemption time `t < t2 - 1` of a busy-interval prefix, the scheduled
job has higher-or-equal priority. -/
theorem scheduled_at_preemption_time_implies_higher_or_equal_priority_lt [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job] [JobReady Job PState], work_bearing_readiness arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ (j : Job) (t1 t2 : instant), busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true →
      preemption_time arr_seq sched t = true → t < t2 - 1 →
    ∀ jhp : Job, scheduled_at sched jhp t = true → JLFP.hep_job jhp j = true := by
  intro PState huni sched JLFP htrans _ _ hwb hresp j t1 t2 hbip t ht hpt hlt jlp hs
  by_contra hnhp
  have ⟨_, _, hnq, _⟩ := hbip
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  apply hnq (t + 1) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  intro j_hp ha hhp hbef
  by_contra hnc
  have hpend : pending sched j_hp t = true := by
    unfold pending has_arrived
    simp only [arrived_before, decide_eq_true_eq] at hbef
    have hncomp : completed_by sched j_hp t = false := by
      cases h : completed_by sched j_hp t
      · rfl
      · exact absurd (completion_monotonic sched j_hp t (t + 1) (Nat.le_succ t) h) hnc
    rw [hncomp]
    simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
    omega'
  exact hnhp (hep_of_pending_hep arr_seq huni sched JLFP htrans hwb hresp j t hpt j_hp ha hhp hpend jlp hs)

/-- At the preemption time `t = t2 - 1` of a busy-interval prefix, the
scheduled job has higher-or-equal priority. -/
theorem scheduled_at_preemption_time_implies_higher_or_equal_priority_eq [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job] [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true →
      preemption_time arr_seq sched t = true → t = t2 - 1 →
    ∀ jhp : Job, scheduled_at sched jhp t = true → JLFP.hep_job jhp j = true := by
  intro PState huni sched JLFP htrans _ _ hwb hvs hresp j ha hpos t1 t2 hbip t ht hpt heq jlp hs
  by_contra hnhp
  have ⟨_, _, hnq, harr⟩ := hbip
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht harr
  rcases Nat.lt_or_ge t1 t with hlt1 | hge1
  · apply hnq t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    intro j_hp ha' hhp hbef
    by_contra hnc
    have hpend : pending sched j_hp t = true := by
      unfold pending has_arrived
      simp only [arrived_before, decide_eq_true_eq] at hbef
      have hncomp : completed_by sched j_hp t = false := by
        cases h : completed_by sched j_hp t
        · rfl
        · exact absurd h hnc
      rw [hncomp]
      simp only [Bool.not_false, Bool.and_true, decide_eq_true_eq]
      omega'
    exact hnhp (hep_of_pending_hep arr_seq huni sched JLFP htrans hwb hresp j t hpt j_hp ha' hhp hpend
      jlp hs)
  · have harrj : job_arrival j = t := by omega'
    have hpend : pending sched j t = true := by
      rw [← harrj]
      exact job_pending_at_arrival sched j (of_decide_eq_true hpos)
        (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs)
    exact hnhp (by
      obtain ⟨j', ha', hr', hhep'⟩ := hwb j t ha hpend
      exact hep_of_pending_hep arr_seq huni sched JLFP htrans hwb hresp j t hpt j' ha' hhep'
        (ready_implies_pending sched j' t hr') jlp hs)

/-- At a preemption time of a busy-interval prefix, the scheduled job has
higher-or-equal priority. -/
theorem scheduled_at_preemption_time_implies_higher_or_equal_priority [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job] [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true →
      preemption_time arr_seq sched t = true →
    ∀ jhp : Job, scheduled_at sched jhp t = true → JLFP.hep_job jhp j = true := by
  intro PState huni sched JLFP htrans _ _ hwb hvs hresp j ha hpos t1 t2 hbip t ht hpt jhp hs
  have ht' := ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  rcases Nat.lt_or_ge t (t2 - 1) with hlt | hge
  · exact scheduled_at_preemption_time_implies_higher_or_equal_priority_lt arr_seq huni sched JLFP htrans
      hwb hresp j t1 t2 hbip t ht hpt hlt jhp hs
  · exact scheduled_at_preemption_time_implies_higher_or_equal_priority_eq arr_seq huni sched JLFP htrans
      hwb hvs hresp j ha hpos t1 t2 hbip t ht hpt (by omega') jhp hs

/-- A job scheduled at a higher-or-equal-priority instant of a busy prefix
arrived after the quiet time `t1`, provided it is not yet complete. -/
private theorem arrived_after_quiet [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} (sched : schedule PState)
    (JLFP : JLFP_policy Job) [JobReady Job PState] (hvs : valid_schedule sched arr_seq)
    (j : Job) (t1 : instant) (hq : quiet_time arr_seq sched j t1)
    (jhp : Job) (t : instant) (hle : t1 ≤ t) (hhp : JLFP.hep_job jhp j = true)
    (hs : scheduled_at sched jhp t = true) : t1 ≤ job_arrival jhp ∧ job_arrival jhp ≤ t := by
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcomp := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hpend := scheduled_implies_pending sched hcomp jhp hmust t hs
  unfold pending has_arrived at hpend
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpend
  refine ⟨?_, hpend.1⟩
  by_contra hlt
  have hc1 : completed_by sched jhp t1 = true :=
    hq jhp (hvs.1 jhp t hs) hhp (by simp only [arrived_before, decide_eq_true_eq]; omega')
  have hct := completion_monotonic sched jhp t1 t hle hc1
  have hns := completed_implies_not_scheduled sched jhp hcomp t hct
  rw [hs] at hns
  exact absurd hns (by decide)

/-- A job scheduled at a preemption time of a busy-interval prefix arrived
inside the prefix. -/
theorem scheduled_at_preemption_time_implies_arrived_between_within_busy_interval [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job] [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true →
      preemption_time arr_seq sched t = true →
    ∀ jhp : Job, scheduled_at sched jhp t = true → arrived_between jhp t1 t2 = true := by
  intro PState huni sched JLFP htrans _ _ hwb hvs hresp j ha hpos t1 t2 hbip t ht hpt jhp hs
  have hhp := scheduled_at_preemption_time_implies_higher_or_equal_priority arr_seq huni sched JLFP
    htrans hwb hvs hresp j ha hpos t1 t2 hbip t ht hpt jhp hs
  have ⟨_, hq, _, _⟩ := hbip
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  have h := arrived_after_quiet arr_seq sched JLFP hvs j t1 hq jhp t ht.1 hhp hs
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]
  omega'

/-- At a preemption time of a busy-interval prefix, some higher-or-equal-priority
job that arrived inside the prefix is scheduled. -/
theorem not_quiet_implies_exists_scheduled_hp_job_at_preemption_point [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job] [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → work_conserving arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true →
      preemption_time arr_seq sched t = true →
      ∃ j_hp : Job, arrived_between j_hp t1 t2 = true ∧ JLFP.hep_job j_hp j = true ∧
        scheduled_at sched j_hp t = true := by
  intro hva PState huni sched JLFP hrefl htrans _ _ hwb hvs hwc hresp j ha hpos t1 t2 hbip t ht hpt
  rcases scheduled_at_cases arr_seq hva sched hvs.1
      (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) t with hidle | ⟨j', hs⟩
  · exact absurd hidle (instant_t_is_not_idle arr_seq hva sched JLFP hrefl hwb hvs hwc j ha hpos t1 t2
      hbip t ht)
  · exact ⟨j', scheduled_at_preemption_time_implies_arrived_between_within_busy_interval arr_seq huni
      sched JLFP htrans hwb hvs hresp j ha hpos t1 t2 hbip t ht hpt j' hs,
      scheduled_at_preemption_time_implies_higher_or_equal_priority arr_seq huni sched JLFP htrans hwb
        hvs hresp j ha hpos t1 t2 hbip t ht hpt j' hs, hs⟩

/-- After a preemption point inside a busy-interval prefix, some
higher-or-equal-priority job is scheduled at every instant of the prefix. -/
theorem not_quiet_implies_exists_scheduled_hp_job_after_preemption_point [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → work_conserving arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ (tp : instant) (t : Nat), preemption_time arr_seq sched tp = true →
      (decide (t1 ≤ tp) && decide (tp < t2)) = true →
      (decide (tp ≤ t) && decide (t < t2)) = true →
      ∃ j_hp : Job, arrived_between j_hp t1 (t + 1) = true ∧ JLFP.hep_job j_hp j = true ∧
        scheduled_at sched j_hp t = true := by
  intro hva PState huni sched JLFP hrefl htrans _ hvpm _ hwb hvs hwc hresp j ha hpos t1 t2 hbip tp t
    hpt htp ht
  have htp' := htp
  have ht' := ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htp' ht'
  rcases scheduled_at_cases arr_seq hva sched hvs.1
      (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) t with hidle | ⟨jhp, hs⟩
  · exact absurd hidle (instant_t_is_not_idle arr_seq hva sched JLFP hrefl hwb hvs hwc j ha hpos t1 t2
      hbip t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'))
  · have hhp : JLFP.hep_job jhp j = true := by
      obtain ⟨prt, hin, hprt, hsch⟩ :=
        scheduling_of_any_segment_starts_with_preemption_time huni arr_seq hva sched hvs hvpm jhp t hs
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
      rcases Nat.lt_or_ge prt t1 with hlt | hle
      · obtain ⟨jlp, _, hhep, hsl⟩ := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
          arr_seq hva huni sched JLFP hrefl htrans hwb hvs hwc hresp j ha hpos t1 t2 hbip tp htp hpt
        have heq := huni jhp jlp sched tp
          (hsch tp (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')) hsl
        subst heq
        exact hhep
      · obtain ⟨jlp, _, hhep, hsl⟩ := not_quiet_implies_exists_scheduled_hp_job_at_preemption_point
          arr_seq hva huni sched JLFP hrefl htrans hwb hvs hwc hresp j ha hpos t1 t2 hbip prt
          (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hprt
        have heq := huni jhp jlp sched prt
          (hsch prt (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')) hsl
        subst heq
        exact hhep
    have ⟨_, hq, _, _⟩ := hbip
    have h := arrived_after_quiet arr_seq sched JLFP hvs j t1 hq jhp t (by omega') hhp hs
    refine ⟨jhp, ?_, hhp, hs⟩
    simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]
    omega'

/-- If a preemption time exists within `K` of the prefix start, then after
`t1 + K` some higher-or-equal-priority job is always scheduled. -/
theorem not_quiet_implies_exists_scheduled_hp_job [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → work_conserving arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ K : duration,
      (∃ pr_t : instant, preemption_time arr_seq sched pr_t = true ∧
        (decide (t1 ≤ pr_t) && decide (pr_t ≤ t1 + K)) = true) →
    ∀ t : Nat, (decide (t1 + K ≤ t) && decide (t < t2)) = true →
      ∃ j_hp : Job, arrived_between j_hp t1 (t + 1) = true ∧ JLFP.hep_job j_hp j = true ∧
        scheduled_at sched j_hp t = true := by
  intro hva PState huni sched JLFP hrefl htrans _ hvpm _ hwb hvs hwc hresp j ha hpos t1 t2 hbip K hex
    t ht
  obtain ⟨prt, hpt, hin⟩ := hex
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hin ht
  exact not_quiet_implies_exists_scheduled_hp_job_after_preemption_point arr_seq hva huni sched JLFP
    hrefl htrans hvpm hwb hvs hwc hresp j ha hpos t1 t2 hbip prt t hpt
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')

end HepAtPt

end Prosa.Analysis.Facts.BusyInterval.HepAtPt
