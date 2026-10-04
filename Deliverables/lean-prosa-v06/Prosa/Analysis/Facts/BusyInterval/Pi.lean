-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/busy_interval/pi.v

import Prosa.Model.Task.Preemption.Parameters
import Prosa.Analysis.Facts.Model.Preemption
import Prosa.Analysis.Facts.BusyInterval.HepAtPt
import Prosa.Analysis.Facts.Model.Uniprocessor
import Prosa.Util.Minmax

namespace Prosa.Analysis.Facts.BusyInterval.Pi

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.Uniprocessor
open Prosa.Analysis.Facts.Model.Preemption
open Prosa.Analysis.Facts.Priority.Inversion
open Prosa.Analysis.Facts.BusyInterval.HepAtPt
open Prosa.Util.Minmax
open Prosa.Util.Sum
open scoped BigOperators

/-! Priority inversion inside a busy interval is caused by a single
lower-priority job and lasts at most until the first preemption time.
Binders follow the elaborated source types: every lemma takes only the section
inputs and hypotheses it uses, in their elaborated order; instance inputs
quantified after a hypothesis are `∀ [..]` binders at that position.
Representation: a Boolean in `Prop` position is `= true`; `~~ b` is
`(!b) = true`; `a <= b < c` is a Boolean conjunction of decides; `t.+1` is
`t + 1`; `ε` is `1`; `x \in s` is `decide (x ∈ s) = true`;
`\max_(x <- xs | P x) F x` is `bigMaxListCond xs P F`. -/

section Pi

variable {Job : JobType} [DecidableEq Job]

/-- A priority inversion at `t` exhibits a scheduled lower-priority job. -/
private theorem pi_witness [JobArrival Job] (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) {PState : ProcessorState Job} (sched : schedule PState)
    (hfrom : jobs_come_from_arrival_sequence sched arr_seq) (hmust : jobs_must_arrive_to_execute sched)
    (JLFP : JLFP_policy Job) (j : Job) (t : instant)
    (hpi : priority_inversion arr_seq sched j t = true) :
    ∃ jlp : Job, scheduled_at sched jlp t = true ∧ (!JLFP.hep_job jlp j) = true := by
  unfold priority_inversion at hpi
  simp only [Bool.and_eq_true, List.any_eq_true] at hpi
  obtain ⟨_, jlp, hin, hnhp⟩ := hpi
  refine ⟨jlp, ?_, hnhp⟩
  rw [← scheduled_jobs_at_iff arr_seq hva sched hfrom hmust jlp t]
  exact decide_eq_true hin

/-- No preemption time lies between the start of a busy-interval prefix and
an instant at which a lower-priority job is scheduled. -/
theorem lower_priority_job_scheduled_implies_no_preemption_time [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ jlp : Job, (!JLFP.hep_job jlp j) = true →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true → scheduled_at sched jlp t = true →
    ∀ t' : Nat, (decide (t1 ≤ t') && decide (t' ≤ t)) = true →
      (!preemption_time arr_seq sched t') = true := by
  intro hva PState huni sched JLFP htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t ht hs t'
    ht'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht ht'
  cases hpt : preemption_time arr_seq sched t'
  · rfl
  · exfalso
    obtain ⟨ptst, hin, hpt', hs'⟩ :=
      scheduling_of_any_segment_starts_with_preemption_time_continuously_sched huni arr_seq hva sched hvs
        hvpm jlp t' t ht'.2 hpt hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    have hhep := scheduled_at_preemption_time_implies_higher_or_equal_priority arr_seq huni sched JLFP
      htrans hwb hvs hresp j ha hpos t1 t2 hbip ptst
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hpt' jlp hs'
    rw [hhep] at hlp
    exact absurd hlp (by decide)

/-- A lower-priority job scheduled inside a busy-interval prefix has been
continuously scheduled since the start of the prefix. -/
theorem lower_priority_job_continuously_scheduled [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ jlp : Job, (!JLFP.hep_job jlp j) = true →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true → scheduled_at sched jlp t = true →
    ∀ t' : Nat, (decide (t1 ≤ t') && decide (t' ≤ t)) = true → scheduled_at sched jlp t' = true := by
  intro hva PState huni sched JLFP htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t ht hs t'
    ht'
  have ht'' := ht'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht''
  exact neg_pt_scheduled_continuously_after arr_seq hva PState huni sched hvs.1
    (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) hvpm jlp t' t hs ht''.2
    (fun x hx => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      exact lower_priority_job_scheduled_implies_no_preemption_time arr_seq hva huni sched JLFP htrans
        hvpm hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t ht hs x
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'))

/-- A lower-priority job scheduled inside a busy-interval prefix arrived
before the prefix. -/
theorem low_priority_job_arrives_before_busy_interval_prefix [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ jlp : Job, (!JLFP.hep_job jlp j) = true →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true → scheduled_at sched jlp t = true →
      job_arrival jlp < t1 := by
  intro hva PState huni sched JLFP htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t ht hs
  have ht' := ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hs1 := lower_priority_job_continuously_scheduled arr_seq hva huni sched JLFP htrans hvpm hwb hvs
    hresp j ha hpos t1 t2 hbip jlp hlp t ht hs t1 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  have harr := has_arrived_scheduled sched jlp hmust t1 hs1
  unfold has_arrived at harr
  simp only [decide_eq_true_eq] at harr
  rcases Nat.lt_or_ge (job_arrival jlp) t1 with hlt | hge
  · exact hlt
  · exfalso
    obtain ⟨pt, hin, hpt, _⟩ :=
      scheduling_of_any_segment_starts_with_preemption_time huni arr_seq hva sched hvs hvpm jlp t hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    have hno := lower_priority_job_scheduled_implies_no_preemption_time arr_seq hva huni sched JLFP htrans
      hvpm hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t ht hs pt
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    rw [hpt] at hno
    exact absurd hno (by decide)

/-- A lower-priority job scheduled inside a busy-interval prefix was also
scheduled before the prefix. -/
theorem low_priority_job_scheduled_before_busy_interval_prefix [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ jlp : Job, (!JLFP.hep_job jlp j) = true →
    ∀ t : instant, (decide (t1 ≤ t) && decide (t < t2)) = true → scheduled_at sched jlp t = true →
      ∃ t' : Nat, t' < t1 ∧ scheduled_at sched jlp t' = true := by
  intro hva PState huni sched JLFP htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t ht hs
  have ht' := ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  have harr := low_priority_job_arrives_before_busy_interval_prefix arr_seq hva huni sched JLFP htrans hvpm
    hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t ht hs
  refine ⟨t1 - 1, by omega', ?_⟩
  have heq : t1 - 1 + 1 = t1 := by omega'
  apply neg_pt_scheduled_at arr_seq hva PState huni sched hvs.1
    (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) hvpm jlp (t1 - 1)
  · rw [heq]
    exact lower_priority_job_continuously_scheduled arr_seq hva huni sched JLFP htrans hvpm hwb hvs hresp
      j ha hpos t1 t2 hbip jlp hlp t ht hs t1 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  · rw [heq]
    exact lower_priority_job_scheduled_implies_no_preemption_time arr_seq hva huni sched JLFP htrans hvpm
      hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t ht hs t1
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')

/-- A lower-priority job arriving inside the prefix is not scheduled before
its arrival window closes. -/
theorem lp_job_should_arrive_early_for_pi [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ jlp : Job, (!JLFP.hep_job jlp j) = true →
    ∀ (t : Nat) (t_arr : instant), decide (jlp ∈ arrivals_between arr_seq t1 t_arr) = true →
      t_arr ≤ t2 → (decide (t1 ≤ t) && decide (t < t_arr)) = true →
      (!scheduled_at sched jlp t) = true := by
  intro hva PState huni sched JLFP htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t t_arr hin
    hle ht
  have ht' := ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  cases hs : scheduled_at sched jlp t
  · rfl
  · exfalso
    have harr := low_priority_job_arrives_before_busy_interval_prefix arr_seq hva huni sched JLFP htrans
      hvpm hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hs
    have hb := in_arrivals_implies_arrived_between arr_seq hva.1 jlp t1 t_arr hin
    simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at hb
    omega'

/-- Without priority inversion at the start of the prefix, no lower-priority
job is scheduled inside it. -/
theorem lower_priority_jobs_never_scheduled_if_no_inversion [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ jlp : Job, (!JLFP.hep_job jlp j) = true →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
      (!priority_inversion arr_seq sched j t1) = true → (!scheduled_at sched jlp t) = true := by
  intro hva PState huni sched JLFP hrefl htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t ht
    hnpi
  have ht' := ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  cases hs : scheduled_at sched jlp t
  · rfl
  · exfalso
    have hs1 := lower_priority_job_continuously_scheduled arr_seq hva huni sched JLFP htrans hvpm hwb hvs
      hresp j ha hpos t1 t2 hbip jlp hlp t ht hs t1
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    have hpi := priority_inversion_hep_job arr_seq hva sched hvs.1
      (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) hrefl j huni t1 jlp hs1
    rw [hpi, hlp] at hnpi
    exact absurd hnpi (by decide)

/-- Before a priority-inversion instant of the prefix there is no preemption
time. -/
theorem no_preemption_time_before_pi [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t_pi : instant, (decide (t1 ≤ t_pi) && decide (t_pi < t2)) = true →
      priority_inversion arr_seq sched j t_pi = true →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t ≤ t_pi)) = true →
      (!preemption_time arr_seq sched t) = true := by
  intro hva PState huni sched JLFP _ htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip t_pi htpi hpi t ht
  obtain ⟨jlp, hs, hlp⟩ := pi_witness arr_seq hva sched hvs.1
    (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) JLFP j t_pi hpi
  exact lower_priority_job_scheduled_implies_no_preemption_time arr_seq hva huni sched JLFP htrans hvpm
    hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t_pi htpi hs t ht

/-- The job causing priority inversion at `t_pi` is scheduled from the start
of the prefix up to `t_pi`. -/
theorem pi_job_remains_scheduled [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t_pi : instant, (decide (t1 ≤ t_pi) && decide (t_pi < t2)) = true →
      priority_inversion arr_seq sched j t_pi = true →
    ∀ jlp : Job, scheduled_at sched jlp t_pi = true →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t ≤ t_pi)) = true → scheduled_at sched jlp t = true := by
  intro hva PState huni sched JLFP _ htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip t_pi htpi hpi jlp1
    hs1 t ht
  obtain ⟨jlp, hs, hlp⟩ := pi_witness arr_seq hva sched hvs.1
    (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) JLFP j t_pi hpi
  have heq := huni jlp1 jlp sched t_pi hs1 hs
  subst heq
  exact lower_priority_job_continuously_scheduled arr_seq hva huni sched JLFP htrans hvpm hwb hvs hresp j
    ha hpos t1 t2 hbip jlp1 hlp t_pi htpi hs t ht

/-- Priority inversion is continuous from the start of the prefix. -/
theorem pi_continuous [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t_pi : instant, (decide (t1 ≤ t_pi) && decide (t_pi < t2)) = true →
      priority_inversion arr_seq sched j t_pi = true →
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t ≤ t_pi)) = true →
      priority_inversion arr_seq sched j t = true := by
  intro hva PState huni sched JLFP hrefl htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip t_pi htpi hpi
    t ht
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  obtain ⟨jlp, hs, hlp⟩ := pi_witness arr_seq hva sched hvs.1 hmust JLFP j t_pi hpi
  have hst := pi_job_remains_scheduled arr_seq hva huni sched JLFP hrefl htrans hvpm hwb hvs hresp j ha
    hpos t1 t2 hbip t_pi htpi hpi jlp hs t ht
  rw [priority_inversion_hep_job arr_seq hva sched hvs.1 hmust hrefl j huni t jlp hst]
  exact hlp

/-- Only one job causes priority inversion inside a busy-interval prefix. -/
theorem only_one_pi_job [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ ts1 : instant, (decide (t1 ≤ ts1) && decide (ts1 < t2)) = true →
    ∀ j1 : Job, scheduled_at sched j1 ts1 = true → (!JLFP.hep_job j1 j) = true →
    ∀ ts2 : instant, (decide (t1 ≤ ts2) && decide (ts2 < t2)) = true →
    ∀ j2 : Job, scheduled_at sched j2 ts2 = true → (!JLFP.hep_job j2 j) = true → j1 = j2 := by
  intro hva PState huni sched JLFP hrefl htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip ts1 hts1 j1
    hs1 hlp1 ts2 hts2 j2 hs2 hlp2
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hts1' := hts1
  have hts2' := hts2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hts1' hts2'
  rcases Nat.le_total ts1 ts2 with hle | hle
  · have hpi : priority_inversion arr_seq sched j ts2 = true := by
      rw [priority_inversion_hep_job arr_seq hva sched hvs.1 hmust hrefl j huni ts2 j2 hs2]; exact hlp2
    exact huni j1 j2 sched ts1 hs1 (pi_job_remains_scheduled arr_seq hva huni sched JLFP hrefl htrans hvpm
      hwb hvs hresp j ha hpos t1 t2 hbip ts2 hts2 hpi j2 hs2 ts1
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'))
  · have hpi : priority_inversion arr_seq sched j ts1 = true := by
      rw [priority_inversion_hep_job arr_seq hva sched hvs.1 hmust hrefl j huni ts1 j1 hs1]; exact hlp1
    exact huni j1 j2 sched ts2 (pi_job_remains_scheduled arr_seq hva huni sched JLFP hrefl htrans hvpm
      hwb hvs hresp j ha hpos t1 t2 hbip ts1 hts1 hpi j1 hs1 ts2
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')) hs2

/-- Either there is no priority inversion in the prefix, or it occurs at its
start. -/
theorem busy_interval_pi_cases [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), reflexive_job_priorities JLFP →
      transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
      cumulative_priority_inversion arr_seq sched j t1 t2 = 0 ∨
        priority_inversion arr_seq sched j t1 = true := by
  intro hva PState huni sched JLFP hrefl htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip
  cases h1 : priority_inversion arr_seq sched j t1
  · left
    unfold cumulative_priority_inversion
    apply Finset.sum_eq_zero
    intro t ht
    rw [Finset.mem_Ico] at ht
    cases hpt : priority_inversion arr_seq sched j t
    · rfl
    · exfalso
      have := pi_continuous arr_seq hva huni sched JLFP hrefl htrans hvpm hwb hvs hresp j ha hpos t1 t2
        hbip t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hpt t1
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
      rw [h1] at this
      exact absurd this (by decide)
  · right; rfl

private theorem le_bigMaxListCond {X : Type _} (xs : List X) (P : X → Bool) (F : X → Nat) (x : X)
    (hx : x ∈ xs) (hP : P x = true) : F x ≤ bigMaxListCond xs P F := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    unfold bigMaxListCond
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hx with h | h
    · subst h; rw [if_pos hP]; exact Nat.le_max_left _ _
    · have := ih h
      unfold bigMaxListCond at this
      split
      · exact Nat.le_trans this (Nat.le_max_right _ _)
      · exact this

private theorem bigMaxListCond_mono {X : Type _} (xs : List X) (P : X → Bool) (F G : X → Nat)
    (h : ∀ x, x ∈ xs → P x = true → F x ≤ G x) : bigMaxListCond xs P F ≤ bigMaxListCond xs P G := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons a xs ih =>
    have ih' := ih (fun x hx hP => h x (List.mem_cons_of_mem a hx) hP)
    unfold bigMaxListCond at ih' ⊢
    simp only [List.foldr_cons]
    split
    · exact max_le_max (h a List.mem_cons_self (by assumption)) ih'
    · exact ih'

/-- The maximum nonpreemptive-segment length (minus one) among the
lower-priority jobs with positive cost that arrived before `t`. -/
def max_lp_nonpreemptive_segment [JobCost Job] (arr_seq : arrival_sequence Job) [JLFP_policy Job]
    [JobPreemptable Job] (j : Job) (t : instant) : Nat :=
  bigMaxListCond (arrivals_before arr_seq t)
    (fun j_lp => (!hep_job j_lp j) && decide (job_cost j_lp > 0))
    (fun j_lp => job_max_nonpreemptive_segment j_lp - 1)

/-- The task-level maximum nonpreemptive segments bound the job-level one. -/
theorem max_np_job_segment_bounded_by_max_np_task_segment {Task : TaskType} [DecidableEq Task]
    [JobTask Job Task] [JobCost Job] (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (sched : schedule PState) (JLFP : JLFP_policy Job) [TaskMaxNonpreemptiveSegment Task]
    [JobPreemptable Job] (j : Job) (t1 : instant) :
    valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      max_lp_nonpreemptive_segment arr_seq j t1 ≤
        bigMaxListCond (arrivals_between arr_seq 0 t1)
          (fun j_lp => (!JLFP.hep_job j_lp j) && decide (0 < job_cost j_lp))
          (fun j_lp => task_max_nonpreemptive_segment (job_task (Task := Task) j_lp) - 1) := by
  intro hvalid
  unfold max_lp_nonpreemptive_segment arrivals_before
  apply bigMaxListCond_mono
  intro x hx _
  have ha := in_arrivals_implies_arrived arr_seq x 0 t1 (decide_eq_true hx)
  have hr := (hvalid.2 x ha).1
  unfold job_respects_max_nonpreemptive_segment at hr
  simp only [decide_eq_true_eq] at hr
  omega'

/-- A higher-or-equal-priority job scheduled at a quiet time `t + 1` was not
scheduled at `t`. -/
theorem hp_job_not_scheduled_before_quiet_time [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) {PState : ProcessorState Job} (sched : schedule PState)
    (JLFP : JLFP_policy Job) [JobReady Job PState] :
    valid_schedule sched arr_seq →
    ∀ (j jhp : Job) (t : Nat), quiet_time arr_seq sched j (t + 1) →
      scheduled_at sched jhp (t + 1) = true → JLFP.hep_job jhp j = true →
      (!scheduled_at sched jhp t) = true := by
  intro hvs j jhp t hq hs1 hhp
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcomp := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  cases hs : scheduled_at sched jhp t
  · rfl
  · exfalso
    have harr := has_arrived_scheduled sched jhp hmust t hs
    unfold has_arrived at harr
    simp only [decide_eq_true_eq] at harr
    have hc := hq jhp (hvs.1 jhp (t + 1) hs1) hhp (by simp only [arrived_before, decide_eq_true_eq]; omega')
    have hns := completed_implies_not_scheduled sched jhp hcomp (t + 1) hc
    rw [hs1] at hns
    exact absurd hns (by decide)

/-- Case 1: an idle start of the prefix is a preemption time. -/
theorem preemption_time_exists_case1 {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) {PState : ProcessorState Job}
    (sched : schedule PState) (JLFP : JLFP_policy Job) [TaskMaxNonpreemptiveSegment Task]
    [JobPreemptable Job] (j : Job) (t1 t2 : instant) :
    busy_interval_prefix arr_seq sched j t1 t2 →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      is_idle arr_seq sched t1 = true →
      ∃ pr_t : instant, preemption_time arr_seq sched pr_t = true ∧
        (decide (t1 ≤ pr_t) && decide (pr_t ≤ t1 + max_lp_nonpreemptive_segment arr_seq j t1)) = true := by
  intro _ _ hidle
  exact ⟨t1, idle_time_is_pt arr_seq sched t1 hidle,
    by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'⟩

/-- Case 2: a higher-or-equal-priority job scheduled at the start of the
prefix makes it a preemption time. -/
theorem preemption_time_exists_case2 {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job) [TaskMaxNonpreemptiveSegment Task]
      [JobPreemptable Job] [JobReady Job PState], valid_schedule sched arr_seq →
    ∀ (j : Job) (t1 t2 : instant), busy_interval_prefix arr_seq sched j t1 t2 →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
    ∀ jhp : Job, scheduled_at sched jhp t1 = true → JLFP.hep_job jhp j = true →
      ∃ pr_t : instant, preemption_time arr_seq sched pr_t = true ∧
        (decide (t1 ≤ pr_t) && decide (pr_t ≤ t1 + max_lp_nonpreemptive_segment arr_seq j t1)) = true := by
  intro hva PState huni sched JLFP _ _ _ hvs j t1 t2 hbip hvalid jhp hs hhp
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  refine ⟨t1, ?_, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'⟩
  have ⟨_, hq, _, _⟩ := hbip
  cases t1 with
  | zero => exact zero_is_pt arr_seq hva PState huni sched hvs.1 hmust hvalid.1
  | succ s =>
    exact first_moment_is_pt arr_seq hva PState huni sched hvs.1 hmust hvalid.1 jhp s
      (hvs.1 jhp (s + 1) hs)
      (hp_job_not_scheduled_before_quiet_time arr_seq sched JLFP hvs j jhp s hq hs hhp) hs

/-- Before the first preemption point `fpt` after the progress at `t1`, the
job is not preemptable. -/
theorem no_intermediate_preemption_point [JobCost Job] {PState : ProcessorState Job}
    (sched : schedule PState) [JobPreemptable Job] (t1 : instant) (jlp : Job) (fpt : instant) :
    (∀ ρ : Nat, (decide (service sched jlp t1 ≤ ρ) &&
        decide (ρ ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - 1))) = true →
      job_preemptable jlp ρ = true → service sched jlp t1 + fpt ≤ ρ) →
    fpt ≤ job_max_nonpreemptive_segment jlp - 1 →
    ∀ ρ : Nat, (decide (service sched jlp t1 ≤ ρ) && decide (ρ < service sched jlp t1 + fpt)) = true →
      (!job_preemptable jlp ρ) = true := by
  intro hfirst hle ρ hρ
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hρ
  cases hp : job_preemptable jlp ρ
  · rfl
  · exfalso
    have := hfirst ρ (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hp
    omega'

/-- The service of a unit-service schedule grows by at most one per instant. -/
private theorem service_during_le_length [JobCost Job] {PState : ProcessorState Job}
    (hunit : unit_service_proc_model PState) (sched : schedule PState) (j : Job) (t1 t2 : instant) :
    service_during sched j t1 t2 ≤ t2 - t1 := by
  unfold service_during
  calc ∑ t ∈ Finset.Ico t1 t2, service_at sched j t ≤ ∑ t ∈ Finset.Ico t1 t2, 1 :=
        Finset.sum_le_sum (fun x _ => hunit j (sched x))
    _ = t2 - t1 := by simp

/-- Up to its first preemption point the job remains scheduled. -/
theorem continuously_scheduled_between_preemption_points {Task : TaskType} [DecidableEq Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    {PState : ProcessorState Job} (sched : schedule PState) [TaskMaxNonpreemptiveSegment Task]
    [JobPreemptable Job] [JobReady Job PState] :
    valid_schedule sched arr_seq →
    ∀ t1 : instant, valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      unit_service_proc_model PState →
    ∀ jlp : Job, scheduled_at sched jlp t1 = true →
    ∀ fpt : instant,
      (∀ ρ : Nat, (decide (service sched jlp t1 ≤ ρ) &&
          decide (ρ ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - 1))) = true →
        job_preemptable jlp ρ = true → service sched jlp t1 + fpt ≤ ρ) →
      fpt ≤ job_max_nonpreemptive_segment jlp - 1 →
    ∀ t' : Nat, (decide (t1 ≤ t') && decide (t' < t1 + fpt)) = true → scheduled_at sched jlp t' = true := by
  intro hvs t1 hvalid hunit jlp hs fpt hfirst hle t' ht'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
  have ha := hvs.1 jlp t1 hs
  have hnps := (hvalid.1 jlp ha).2.2.1
  apply hnps
  have hcat := service_cat sched jlp t1 t' ht'.1
  have hdur := service_during_le_length hunit sched jlp t1 t'
  exact no_intermediate_preemption_point sched t1 jlp fpt hfirst hle _
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')

/-- With ideal progress, the job reaches its first preemption point at
`t1 + fpt`, which is therefore a preemption time. -/
theorem first_preemption_time {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) [TaskMaxNonpreemptiveSegment Task] [JobPreemptable Job],
      valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], valid_schedule sched arr_seq →
    ∀ t1 : instant, valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      unit_service_proc_model PState →
    ∀ jlp : Job, scheduled_at sched jlp t1 = true →
    ∀ fpt : instant, job_preemptable jlp (service sched jlp t1 + fpt) = true →
      (∀ ρ : Nat, (decide (service sched jlp t1 ≤ ρ) &&
          decide (ρ ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - 1))) = true →
        job_preemptable jlp ρ = true → service sched jlp t1 + fpt ≤ ρ) →
      fpt ≤ job_max_nonpreemptive_segment jlp - 1 →
      ideal_progress_proc_model PState → preemption_time arr_seq sched (t1 + fpt) = true := by
  intro hva PState huni sched _ _ hvpm _ hvs t1 hvalid hunit jlp hs fpt hpp hfirst hle hideal
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcont := continuously_scheduled_between_preemption_points (Task := Task) arr_seq sched hvs t1 hvalid
    hunit jlp hs fpt hfirst hle
  rcases scheduled_at_cases arr_seq hva sched hvs.1 hmust (t1 + fpt) with hidle | ⟨j', hs'⟩
  · exact idle_time_is_pt arr_seq sched _ hidle
  · by_cases heq : jlp = j'
    · subst heq
      have hsj := scheduled_job_at_scheduled_at arr_seq hva sched hvs.1 hmust huni jlp (t1 + fpt)
      rw [hs'] at hsj
      have hsome : scheduled_job_at arr_seq sched (t1 + fpt) = some jlp := of_decide_eq_true hsj
      unfold preemption_time
      rw [hsome]
      dsimp only
      have hdur : service_during sched jlp t1 (t1 + fpt) = fpt := by
        unfold service_during
        refine Eq.trans (Finset.sum_congr rfl ?_) (sum_of_ones t1 fpt)
        intro x hx
        rw [Finset.mem_Ico] at hx
        have hsx := hcont x (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
        exact Nat.le_antisymm (hunit jlp (sched x)) (hideal jlp (sched x) hsx)
      have hcat := service_cat sched jlp t1 (t1 + fpt) (Nat.le_add_right _ _)
      rw [← hcat, hdur]
      exact hpp
    · rcases Nat.eq_zero_or_pos fpt with h0 | hpos
      · subst h0
        exact absurd (huni jlp j' sched (t1 + 0) (by simpa using hs) hs') heq
      · obtain ⟨sm, rfl⟩ : ∃ sm, fpt = sm + 1 := ⟨fpt - 1, by omega'⟩
        have hjlp := hcont (t1 + sm) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
        have hns := scheduled_job_at_neq huni sched jlp j' (t1 + sm) (decide_eq_true heq) hjlp
        rw [show t1 + (sm + 1) = t1 + sm + 1 by omega'] at hs' ⊢
        exact first_moment_is_pt arr_seq hva PState huni sched hvs.1 hmust hvpm j' (t1 + sm)
          (hvs.1 j' _ hs') hns hs'

/-- The first preemption point of a lower-priority job scheduled at `t1` lies
within the maximum lower-priority nonpreemptive segment. -/
theorem preemption_time_le_max_len_of_np_segment [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ jlp : Job, scheduled_at sched jlp t1 = true → (!JLFP.hep_job jlp j) = true →
    ∀ fpt : instant, job_preemptable jlp (service sched jlp t1 + fpt) = true →
      fpt ≤ job_max_nonpreemptive_segment jlp - 1 →
      (decide (t1 ≤ t1 + fpt) &&
        decide (t1 + fpt ≤ t1 + max_lp_nonpreemptive_segment arr_seq j t1)) = true := by
  intro hva PState huni sched JLFP htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip jlp hs hlp fpt _ hle
  have hcomp := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hlt12 := hbip.1
  have harr := low_priority_job_arrives_before_busy_interval_prefix arr_seq hva huni sched JLFP htrans hvpm
    hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp t1
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hs
  have hin : jlp ∈ arrivals_before arr_seq t1 := of_decide_eq_true
    (arrived_between_implies_in_arrivals arr_seq hva.1 jlp 0 t1 (hvs.1 jlp t1 hs)
      (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega'))
  have hcost := service_lt_cost sched jlp hcomp t1 hs
  have hmax := le_bigMaxListCond (arrivals_before arr_seq t1)
    (fun j_lp => (!JLFP.hep_job j_lp j) && decide (job_cost j_lp > 0))
    (fun j_lp => job_max_nonpreemptive_segment j_lp - 1) jlp hin
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hlp, by omega'⟩)
  have : max_lp_nonpreemptive_segment arr_seq j t1 = bigMaxListCond (arrivals_before arr_seq t1)
    (fun j_lp => (!JLFP.hep_job j_lp j) && decide (job_cost j_lp > 0))
    (fun j_lp => job_max_nonpreemptive_segment j_lp - 1) := rfl
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  omega'

/-- Case 3: a lower-priority job scheduled at the start of the prefix reaches
a preemption point within the maximum lower-priority nonpreemptive segment. -/
theorem preemption_time_exists_case3 {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [TaskMaxNonpreemptiveSegment Task] [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      unit_service_proc_model PState →
    ∀ jlp : Job, scheduled_at sched jlp t1 = true → (!JLFP.hep_job jlp j) = true →
      ideal_progress_proc_model PState →
      ∃ pr_t : instant, preemption_time arr_seq sched pr_t = true ∧
        (decide (t1 ≤ pr_t) && decide (pr_t ≤ t1 + max_lp_nonpreemptive_segment arr_seq j t1)) = true := by
  intro hva PState huni sched JLFP htrans _ _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip hvalid hunit jlp
    hs hlp hideal
  classical
  have hcomp := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have haj := hvs.1 jlp t1 hs
  have hmost := service_at_most_cost sched hcomp jlp hunit t1
  obtain ⟨pp, hpp, hppre⟩ := (hvalid.2 jlp haj).2 (service sched jlp t1)
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpp
  have hex : ∃ n, service sched jlp t1 ≤ n ∧
      n ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - 1) ∧ job_preemptable jlp n = true :=
    ⟨pp, hpp.1, hpp.2, hppre⟩
  have hspec := Nat.find_spec hex
  have hmin : ∀ n, n < Nat.find hex → ¬ (service sched jlp t1 ≤ n ∧
      n ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - 1) ∧ job_preemptable jlp n = true) :=
    fun n hn => Nat.find_min hex hn
  have hfpt : service sched jlp t1 + (Nat.find hex - service sched jlp t1) = Nat.find hex := by omega'
  have hfirst : ∀ ρ : Nat, (decide (service sched jlp t1 ≤ ρ) &&
      decide (ρ ≤ service sched jlp t1 + (job_max_nonpreemptive_segment jlp - 1))) = true →
      job_preemptable jlp ρ = true →
      service sched jlp t1 + (Nat.find hex - service sched jlp t1) ≤ ρ := by
    intro ρ hρ hpρ
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hρ
    rw [hfpt]
    by_contra hlt
    exact hmin ρ (by omega') ⟨hρ.1, hρ.2, hpρ⟩
  have hle : Nat.find hex - service sched jlp t1 ≤ job_max_nonpreemptive_segment jlp - 1 := by omega'
  have hppre' : job_preemptable jlp (service sched jlp t1 + (Nat.find hex - service sched jlp t1)) = true := by
    rw [hfpt]; exact hspec.2.2
  refine ⟨t1 + (Nat.find hex - service sched jlp t1), ?_, ?_⟩
  · exact first_preemption_time (Task := Task) arr_seq hva huni sched hvpm hvs t1 hvalid hunit jlp hs _
      hppre' hfirst hle hideal
  · exact preemption_time_le_max_len_of_np_segment arr_seq hva huni sched JLFP htrans hvpm hwb hvs hresp j
      ha hpos t1 t2 hbip jlp hs hlp _ hppre' hle

/-- There is a preemption time within the maximum lower-priority
nonpreemptive segment after the start of the prefix. -/
theorem preemption_time_exists {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [TaskMaxNonpreemptiveSegment Task] [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      unit_service_proc_model PState → ideal_progress_proc_model PState →
      ∃ pr_t : instant, preemption_time arr_seq sched pr_t = true ∧
        (decide (t1 ≤ pr_t) && decide (pr_t ≤ t1 + max_lp_nonpreemptive_segment arr_seq j t1)) = true := by
  intro hva PState huni sched JLFP htrans _ _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip hvalid hunit hideal
  rcases scheduled_at_cases arr_seq hva sched hvs.1
      (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) t1 with hidle | ⟨s, hs⟩
  · exact preemption_time_exists_case1 (Task := Task) arr_seq sched JLFP j t1 t2 hbip hvalid hidle
  · cases hp : JLFP.hep_job s j
    · exact preemption_time_exists_case3 (Task := Task) arr_seq hva huni sched JLFP htrans hvpm hwb hvs
        hresp j ha hpos t1 t2 hbip hvalid hunit s hs (by rw [hp]; rfl) hideal
    · exact preemption_time_exists_case2 (Task := Task) arr_seq hva huni sched JLFP hvs j t1 t2 hbip
        hvalid s hs hp

/-- After a preemption point inside the prefix there is no priority
inversion. -/
theorem no_priority_inversion_after_preemption_point [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ ppt : instant, preemption_time arr_seq sched ppt = true → t1 ≤ ppt →
    ∀ t : Nat, (decide (ppt ≤ t) && decide (t < t2)) = true →
      (!priority_inversion arr_seq sched j t) = true := by
  intro hva PState huni sched JLFP htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip ppt hppt hle t ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  cases hpi : priority_inversion arr_seq sched j t
  · rfl
  · exfalso
    obtain ⟨jlp, hs, hlp⟩ := pi_witness arr_seq hva sched hvs.1
      (valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs) JLFP j t hpi
    obtain ⟨ptst, hin, hpt, hs'⟩ :=
      scheduling_of_any_segment_starts_with_preemption_time_continuously_sched huni arr_seq hva sched hvs
        hvpm jlp ppt t ht.1 hppt hs
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hin
    have hhep := scheduled_at_preemption_time_implies_higher_or_equal_priority arr_seq huni sched JLFP
      htrans hwb hvs hresp j ha hpos t1 t2 hbip ptst
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hpt jlp hs'
    rw [hhep] at hlp
    exact absurd hlp (by decide)

/-- Hence the cumulative priority inversion in the prefix is attained before
the preemption point. -/
theorem priority_inversion_occurs_only_till_preemption_point [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ {PState : ProcessorState Job}, uniprocessor_model PState →
    ∀ (sched : schedule PState) (JLFP : JLFP_policy Job), transitive_job_priorities JLFP →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
    ∀ [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq → respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ ppt : instant, preemption_time arr_seq sched ppt = true → t1 ≤ ppt →
      cumulative_priority_inversion arr_seq sched j t1 t2 ≤
        cumulative_priority_inversion arr_seq sched j t1 ppt := by
  intro hva PState huni sched JLFP htrans _ hvpm _ hwb hvs hresp j ha hpos t1 t2 hbip ppt hppt hle
  unfold cumulative_priority_inversion
  rcases Nat.le_total t2 ppt with h2 | h2
  · apply Finset.sum_le_sum_of_subset
    intro x hx
    simp only [Finset.mem_Ico] at hx ⊢
    omega'
  · rw [← Finset.sum_Ico_consecutive _ hle h2]
    have hz : ∑ t ∈ Finset.Ico ppt t2, (priority_inversion arr_seq sched j t).toNat = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      rw [Finset.mem_Ico] at ht
      have := no_priority_inversion_after_preemption_point arr_seq hva huni sched JLFP htrans hvpm hwb hvs
        hresp j ha hpos t1 t2 hbip ppt hppt hle t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
      rw [this]; rfl
    rw [hz]
    omega'

end Pi

end Prosa.Analysis.Facts.BusyInterval.Pi
