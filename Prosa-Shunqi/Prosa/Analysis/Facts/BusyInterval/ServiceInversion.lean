-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/busy_interval/service_inversion.v

import Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix
import Prosa.Analysis.Facts.BusyInterval.Pi
import Prosa.Analysis.Facts.Behavior.Supply

namespace Prosa.Analysis.Facts.BusyInterval.ServiceInversion

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
open Prosa.Model.Processor.Supply
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.Service
open Prosa.Analysis.Definitions.ServiceInversion.Pred
open Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Behavior.Supply
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Model.Preemption
open Prosa.Analysis.Facts.BusyInterval.HepAtPt
open Prosa.Analysis.Facts.BusyInterval.Pi
open Prosa.Util.Minmax
open scoped BigOperators

/-! Service inversion inside busy intervals: basic facts, its relation to
priority inversion, and a bound by the maximum lower-priority nonpreemptive
segment.
Binders follow the elaborated source types: every lemma takes only the section
inputs and hypotheses it uses, in their elaborated order; instance inputs
quantified after a hypothesis are `∀ [..]` binders at that position.  Where the
source uses a JLFP policy with a JLDP-based definition, the policy is coerced
by the accepted `JLFP_to_JLDP`.
Representation: a Boolean in `Prop` position is `= true`; `~~ b` is
`(!b) = true`; `a <= b < c` is a Boolean conjunction of decides; `ε` is `1`. -/

section ServiceInversion

variable {Job : JobType} [DecidableEq Job]

/-- A service inversion exhibits a served lower-priority job while `j` is not
served. -/
private theorem si_witness {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) [JLDP_policy Job] (j : Job) (t : instant)
    (h : service_inversion arr_seq sched j t = true) :
    ¬ j ∈ served_jobs_at arr_seq sched t ∧
      ∃ s, s ∈ served_jobs_at arr_seq sched t ∧ (!hep_job_at t s j) = true := by
  unfold service_inversion at h
  simp only [Bool.and_eq_true, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not] at h
  obtain ⟨hn, s, hs, hlp⟩ := h
  exact ⟨hn, s, hs, by simpa using hlp⟩

/-- A blackout excludes service inversion. -/
theorem blackout_implies_no_service_inversion {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) (sched : schedule PState) (JLDP : JLDP_policy Job) (j : Job)
    (t : instant) :
    is_blackout sched t = true → (!service_inversion arr_seq sched j t) = true := by
  intro hb
  cases h : service_inversion arr_seq sched j t
  · rfl
  · exfalso
    obtain ⟨_, s, hs, _⟩ := si_witness arr_seq sched j t h
    have hr := served_at_and_receives_service_consistent arr_seq sched s t (decide_eq_true hs)
    have hsup := receives_service_implies_has_supply sched s t hr
    unfold is_blackout at hb
    rw [hsup] at hb
    exact absurd hb (by decide)

/-- An idle instant excludes service inversion. -/
theorem idle_implies_no_service_inversion [JobArrival Job] {PState : ProcessorState Job}
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ (JLDP : JLDP_policy Job) (j : Job) (t : instant),
      is_idle arr_seq sched t = true → (!service_inversion arr_seq sched j t) = true := by
  intro hva sched hfrom hmust JLDP j t hidle
  cases h : service_inversion arr_seq sched j t
  · rfl
  · exfalso
    obtain ⟨_, s, hs, _⟩ := si_witness arr_seq sched j t h
    have hr := served_at_and_receives_service_consistent arr_seq sched s t (decide_eq_true hs)
    have hn := no_service_received_when_idle arr_seq hva sched hfrom hmust s t hidle
    rw [hr] at hn
    exact absurd hn (by decide)

/-- A job receiving service suffers no service inversion. -/
theorem receives_service_implies_no_service_inversion {PState : ProcessorState Job} :
    uniprocessor_model PState →
    ∀ (arr_seq : arrival_sequence Job) (sched : schedule PState) (JLDP : JLDP_policy Job),
      reflexive_priorities JLDP →
    ∀ (j : Job) (t : instant),
      receives_service_at sched j t = true → (!service_inversion arr_seq sched j t) = true := by
  intro huni arr_seq sched JLDP hrefl j t hr
  cases h : service_inversion arr_seq sched j t
  · rfl
  · exfalso
    obtain ⟨_, s, hs, hlp⟩ := si_witness arr_seq sched j t h
    have hrs := served_at_and_receives_service_consistent arr_seq sched s t (decide_eq_true hs)
    have heq := only_one_job_receives_service_at_uni huni sched j s t hr hrs
    subst heq
    rw [hrefl t j] at hlp
    exact absurd hlp (by decide)

/-- Cumulative service inversion splits at any intermediate instant. -/
theorem service_inversion_cat {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (JLDP : JLDP_policy Job) (j : Job) (t1 t2 t : instant) :
    t1 ≤ t → t ≤ t2 →
      cumulative_service_inversion arr_seq sched j t1 t2 =
        cumulative_service_inversion arr_seq sched j t1 t +
          cumulative_service_inversion arr_seq sched j t t2 := by
  intro h1 h2
  unfold cumulative_service_inversion
  rw [Finset.sum_Ico_consecutive _ h1 h2]

/-- Cumulative service inversion grows with the interval. -/
theorem service_inversion_widen {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) (JLDP : JLDP_policy Job) (j : Job) (al ar bl br : instant) :
    bl ≤ al → ar ≤ br →
      cumulative_service_inversion arr_seq sched j al ar ≤
        cumulative_service_inversion arr_seq sched j bl br := by
  intro h1 h2
  unfold cumulative_service_inversion
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_Ico] at hx ⊢
  omega'

/-- With supply at `t` and `j` scheduled, service inversion of `j'` is exactly
`j` having lower priority. -/
theorem service_inversion_supply_sched [JobArrival Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → fully_consuming_proc_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ JLDP : JLDP_policy Job, reflexive_priorities JLDP →
    ∀ t : instant, has_supply sched t = true →
    ∀ j j' : Job, scheduled_at sched j t = true →
      service_inversion arr_seq sched j' t = !hep_job_at t j j' := by
  intro huni hfc arr_seq hva sched hfrom hmust JLDP hrefl t hsup j j' hs
  have hr := ideal_progress_inside_supplies hfc sched j t hsup hs
  cases h : service_inversion arr_seq sched j' t
  · -- no service inversion: then `j` has higher-or-equal priority than `j'`
    cases hh : hep_job_at t j j'
    · exfalso
      have hjin := receives_service_and_served_at_consistent arr_seq hva sched hfrom hmust j t hr
      have hn : ¬ j' ∈ served_jobs_at arr_seq sched t := by
        intro hin
        have hr' := served_at_and_receives_service_consistent arr_seq sched j' t (decide_eq_true hin)
        have heq := only_one_job_receives_service_at_uni huni sched j j' t hr hr'
        subst heq
        rw [hrefl t j] at hh
        exact absurd hh (by decide)
      have : service_inversion arr_seq sched j' t = true := by
        unfold service_inversion
        simp only [Bool.and_eq_true, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not]
        exact ⟨hn, j, of_decide_eq_true hjin, by simp [hh]⟩
      rw [h] at this
      exact absurd this (by decide)
    · rfl
  · obtain ⟨_, s, hs', hlp⟩ := si_witness arr_seq sched j' t h
    have hrs := served_at_and_receives_service_consistent arr_seq sched s t (decide_eq_true hs')
    have heq := only_one_job_receives_service_at_uni huni sched s j t hrs hr
    subst heq
    exact hlp.symm

/-- Service inversion implies priority inversion. -/
theorem service_inv_implies_priority_inv [JobArrival Job] {PState : ProcessorState Job} :
    uniprocessor_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ JLFP : JLFP_policy Job, reflexive_job_priorities JLFP →
    ∀ (j : Job) (t : instant),
      @service_inversion Job _ PState arr_seq sched (JLFP_to_JLDP (JLFP := JLFP)) j t = true →
      priority_inversion arr_seq sched j t = true := by
  intro huni arr_seq hva sched hfrom hmust JLFP hrefl j t h
  obtain ⟨_, s, hs, hlp⟩ := si_witness arr_seq sched j t h
  have hrs := served_at_and_receives_service_consistent arr_seq sched s t (decide_eq_true hs)
  have hss : scheduled_at sched s t = true :=
    service_at_implies_scheduled_at sched s t (by unfold receives_service_at at hrs; exact of_decide_eq_true hrs)
  have hlp' : (!JLFP.hep_job s j) = true := hlp
  unfold priority_inversion
  simp only [Bool.and_eq_true, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not]
  refine ⟨?_, s, ?_, by simpa using hlp'⟩
  · intro hin
    have hsj : scheduled_at sched j t = true := by
      rw [← scheduled_jobs_at_iff arr_seq hva sched hfrom hmust j t]; exact decide_eq_true hin
    have heq := huni s j sched t hss hsj
    subst heq
    rw [hrefl s] at hlp'
    exact absurd hlp' (by decide)
  · have := scheduled_jobs_at_iff arr_seq hva sched hfrom hmust s t
    rw [hss] at this
    exact of_decide_eq_true this

/-- Hence cumulative service inversion is at most cumulative priority
inversion. -/
theorem cumul_service_inv_le_cumul_priority_inv [JobArrival Job] {PState : ProcessorState Job} :
    uniprocessor_model PState →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ sched : schedule PState,
      jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
    ∀ JLFP : JLFP_policy Job, reflexive_job_priorities JLFP →
    ∀ (j : Job) (t1 t2 : instant),
      @cumulative_service_inversion Job _ PState arr_seq sched (JLFP_to_JLDP (JLFP := JLFP)) j t1 t2 ≤
        cumulative_priority_inversion arr_seq sched j t1 t2 := by
  intro huni arr_seq hva sched hfrom hmust JLFP hrefl j t1 t2
  unfold cumulative_service_inversion cumulative_priority_inversion
  apply Finset.sum_le_sum
  intro t _
  cases h : @service_inversion Job _ PState arr_seq sched (JLFP_to_JLDP (JLFP := JLFP)) j t
  · exact Nat.zero_le _
  · rw [service_inv_implies_priority_inv huni arr_seq hva sched hfrom hmust JLFP hrefl j t h]

/-- Introduction form of a service inversion. -/
private theorem si_intro {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) [JLDP_policy Job] (j s : Job) (t : instant)
    (hn : ¬ j ∈ served_jobs_at arr_seq sched t) (hs : s ∈ served_jobs_at arr_seq sched t)
    (hlp : (!hep_job_at t s j) = true) : service_inversion arr_seq sched j t = true := by
  unfold service_inversion
  simp only [Bool.and_eq_true, List.any_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_false_iff_not]
  exact ⟨hn, s, hs, by simpa using hlp⟩

/-- A positive cumulative service inversion exhibits an inversion instant. -/
private theorem si_pos_witness {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
    (sched : schedule PState) [JLDP_policy Job] (j : Job) (t1 t : instant)
    (h : 0 < cumulative_service_inversion arr_seq sched j t1 t) :
    ∃ t', t1 ≤ t' ∧ t' < t ∧ service_inversion arr_seq sched j t' = true := by
  by_contra hno
  have h0 : cumulative_service_inversion arr_seq sched j t1 t = 0 := by
    unfold cumulative_service_inversion
    apply Finset.sum_eq_zero
    intro x hx
    rw [Finset.mem_Ico] at hx
    cases hsi : service_inversion arr_seq sched j x
    · rfl
    · exact absurd ⟨x, hx.1, hx.2, hsi⟩ hno
  omega'

/-- Without preemption times in `[a, b)` and with `jlp` scheduled somewhere in
it, the cumulative service inversion over `[a, b)` is at most the service of
`jlp` there. -/
private theorem no_pt_si_bounded [JobArrival Job] [JobCost Job] [JobPreemptable Job] {PState : ProcessorState Job}
    (huni : uniprocessor_model PState) (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) (sched : schedule PState)
    (hfrom : jobs_come_from_arrival_sequence sched arr_seq) (hmust : jobs_must_arrive_to_execute sched)
    (hvpm : valid_preemption_model arr_seq sched) [JLDP : JLDP_policy Job] (j jlp : Job) (a b : instant)
    (hnpt : ∀ x : Nat, (decide (a ≤ x) && decide (x < b)) = true →
      (!preemption_time arr_seq sched x) = true)
    (hsched : ∃ x, (decide (a ≤ x) && decide (x < b)) = true ∧ scheduled_at sched jlp x = true) :
    cumulative_service_inversion arr_seq sched j a b ≤ service_during sched jlp a b := by
  obtain ⟨x0, hx0, hs0⟩ := hsched
  unfold cumulative_service_inversion service_during
  apply Finset.sum_le_sum
  intro x hx
  rw [Finset.mem_Ico] at hx
  cases hsi : service_inversion arr_seq sched j x
  · exact Nat.zero_le _
  · obtain ⟨_, h, hin, _⟩ := si_witness arr_seq sched j x hsi
    have hr := served_at_and_receives_service_consistent arr_seq sched h x (decide_eq_true hin)
    have hpos : 0 < service_at sched h x := by
      unfold receives_service_at at hr; exact of_decide_eq_true hr
    have hsh := service_at_implies_scheduled_at sched h x hpos
    have hsj := neg_pt_scheduled_continuous arr_seq hva PState huni sched hfrom hmust hvpm jlp a b x0 x
      hx0 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hnpt hs0
    have heq := huni h jlp sched x hsh hsj
    subst heq
    exact hpos

/-- Inside a busy-interval prefix, the cumulative service inversion is caused
by a single lower-priority job that arrived before the prefix. -/
theorem cumulative_service_inversion_from_one_job [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ JLFP : JLFP_policy Job, reflexive_job_priorities JLFP → transitive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : instant, t ≤ t2 →
      0 < @cumulative_service_inversion Job _ PState arr_seq sched (JLFP_to_JLDP (JLFP := JLFP)) j t1 t →
      ∃ jlp : Job, job_arrival jlp < t1 ∧ (!JLFP.hep_job jlp j) = true ∧
        @cumulative_service_inversion Job _ PState arr_seq sched (JLFP_to_JLDP (JLFP := JLFP)) j t1 t =
          service_during sched jlp t1 t := by
  intro huni hunit JLFP hrefl htrans arr_seq hva sched _ hwb hvs _ hvpm hresp j ha hpos t1 t2 hbip t hle
    hcsi
  have hfrom := hvs.1
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  obtain ⟨tx, hto1, hto2, hsi⟩ := si_pos_witness arr_seq sched j t1 t hcsi
  obtain ⟨_, jlp, hin, hlp⟩ := si_witness arr_seq sched j tx hsi
  have hlp' : (!JLFP.hep_job jlp j) = true := hlp
  have hr := served_at_and_receives_service_consistent arr_seq sched jlp tx (decide_eq_true hin)
  have hs : scheduled_at sched jlp tx = true :=
    service_at_implies_scheduled_at sched jlp tx (by unfold receives_service_at at hr; exact of_decide_eq_true hr)
  have hto : (decide (t1 ≤ tx) && decide (tx < t2)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'
  refine ⟨jlp, low_priority_job_arrives_before_busy_interval_prefix arr_seq hva huni sched JLFP htrans hvpm
    hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp' tx hto hs, hlp', ?_⟩
  unfold cumulative_service_inversion service_during
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.mem_Ico] at hx
  rcases unit_supply_proc_service_case sched hunit jlp x with hz | h1
  · rw [hz]
    cases hsx : @service_inversion Job _ PState arr_seq sched (JLFP_to_JLDP (JLFP := JLFP)) j x
    · rfl
    · exfalso
      obtain ⟨_, joo, hinoo, hlpoo⟩ := si_witness arr_seq sched j x hsx
      have hroo := served_at_and_receives_service_consistent arr_seq sched joo x (decide_eq_true hinoo)
      have hsoo : scheduled_at sched joo x = true :=
        service_at_implies_scheduled_at sched joo x
          (by unfold receives_service_at at hroo; exact of_decide_eq_true hroo)
      have heq := only_one_pi_job arr_seq hva huni sched JLFP hrefl htrans hvpm hwb hvs hresp j ha hpos t1 t2
        hbip tx hto jlp hs hlp' x (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') joo hsoo hlpoo
      subst heq
      unfold receives_service_at at hroo
      rw [hz] at hroo
      exact absurd hroo (by decide)
  · rw [h1]
    have hrx : receives_service_at sched jlp x = true := by
      unfold receives_service_at; rw [h1]; decide
    have hnj : ¬ j ∈ served_jobs_at arr_seq sched x := by
      intro hj
      have hrj := served_at_and_receives_service_consistent arr_seq sched j x (decide_eq_true hj)
      have heq := only_one_job_receives_service_at_uni huni sched j jlp x hrj hrx
      subst heq
      rw [hrefl j] at hlp'
      exact absurd hlp' (by decide)
    have hinx := receives_service_and_served_at_consistent arr_seq hva sched hfrom hmust jlp x hrx
    rw [si_intro arr_seq sched j jlp x hnj (of_decide_eq_true hinx) hlp']
    rfl

/-- The maximum over a conditioned list bounds each qualifying element. -/
private theorem si_le_bigMaxListCond {X : Type _} (xs : List X) (P : X → Bool) (F : X → Nat) (x : X)
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

/-- The preemption time at an instant where `jlp` is the scheduled job is the
preemptability of `jlp` at its current service. -/
private theorem pt_of_scheduled [JobArrival Job] [JobPreemptable Job] {PState : ProcessorState Job}
    (huni : uniprocessor_model PState) (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) (sched : schedule PState)
    (hfrom : jobs_come_from_arrival_sequence sched arr_seq) (hmust : jobs_must_arrive_to_execute sched)
    (jlp : Job) (x : instant) (hs : scheduled_at sched jlp x = true) :
    preemption_time arr_seq sched x = job_preemptable jlp (service sched jlp x) := by
  have hsome : scheduled_job_at arr_seq sched x = some jlp :=
    of_decide_eq_true ((scheduled_job_at_scheduled_at arr_seq hva sched hfrom hmust huni jlp x).trans hs)
  unfold preemption_time
  rw [hsome]

/-- The service of a lower-priority job inside a busy-interval prefix is at
most its maximum nonpreemptive segment minus one. -/
theorem lp_job_bounded_service {Task : TaskType} [DecidableEq Task] [TaskMaxNonpreemptiveSegment Task]
    [JobTask Job Task] [JobArrival Job] [JobCost Job] {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ JLFP : JLFP_policy Job, transitive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ jlp : Job, arrives_in arr_seq jlp → (!JLFP.hep_job jlp j) = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : Nat, t ≤ t2 → service_during sched jlp t1 t ≤ job_max_nonpreemptive_segment jlp - 1 := by
  intro huni hunit JLFP htrans arr_seq hva sched _ hwb hvs _ hvpm hvm hresp j ha hpos jlp hjlp hlp t1 t2
    hbip t hle
  have hfrom := hvs.1
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  have hcomp := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hus := unit_supply_is_unit_service PState hunit
  rcases Nat.eq_zero_or_pos (service_during sched jlp t1 t) with hz | hsd
  · rw [hz]; exact Nat.zero_le _
  obtain ⟨st, hst, hs⟩ := cumulative_service_implies_scheduled sched jlp t1 t hsd
  have hst' := hst
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hst'
  have hst2 : (decide (t1 ≤ st) && decide (st < t2)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'
  have hcost := service_at_most_cost sched hcomp jlp hus t1
  obtain ⟨σ, hσ, hpp⟩ := (hvm.2 jlp hjlp).2 (service sched jlp t1)
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hσ
  have hcat := service_cat sched jlp t1 t (by omega')
  rcases Nat.lt_or_ge (service sched jlp t) σ with hsmall | hbig
  · omega'
  · rcases Nat.lt_or_ge σ (service sched jlp t) with hgt | hle'
    · exfalso
      obtain ⟨pt, hpt, hEQ⟩ := exists_intermediate_service hus sched jlp t σ hgt
      have hnpt := lower_priority_job_scheduled_implies_no_preemption_time arr_seq hva huni sched JLFP htrans
        hvpm hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp st hst2 hs t1
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
      have hLEpt : t1 ≤ pt := by
        by_contra hlt
        have hmono := service_monotonic sched jlp pt t1 (by omega')
        have hEQ1 : service sched jlp t1 = σ := by omega'
        have hs1 := lower_priority_job_continuously_scheduled arr_seq hva huni sched JLFP htrans hvpm hwb hvs
          hresp j ha hpos t1 t2 hbip jlp hlp st hst2 hs t1
          (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
        have hPT := pt_of_scheduled huni arr_seq hva sched hfrom hmust jlp t1 hs1
        rw [hEQ1, hpp] at hPT
        rw [hPT] at hnpt
        exact absurd hnpt (by decide)
      obtain ⟨t', ht', hserv', hs'⟩ := kth_scheduling_time sched jlp pt t σ hEQ hgt
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
      have hPT := pt_of_scheduled huni arr_seq hva sched hfrom hmust jlp t' hs'
      rw [hserv', hpp] at hPT
      have hhep := scheduled_at_preemption_time_implies_higher_or_equal_priority arr_seq huni sched JLFP
        htrans hwb hvs hresp j ha hpos t1 t2 hbip t'
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hPT jlp hs'
      rw [hhep] at hlp
      exact absurd hlp (by decide)
    · omega'

/-- Hence it is at most the maximum lower-priority nonpreemptive segment. -/
theorem lp_job_bounded_service_max {Task : TaskType} [DecidableEq Task]
    [TaskMaxNonpreemptiveSegment Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ JLFP : JLFP_policy Job, transitive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ j : Job, arrives_in arr_seq j → job_cost_positive j = true →
    ∀ jlp : Job, arrives_in arr_seq jlp → (!JLFP.hep_job jlp j) = true →
    ∀ t1 t2 : instant, busy_interval_prefix arr_seq sched j t1 t2 →
    ∀ t : Nat, t ≤ t2 → service_during sched jlp t1 t ≤ max_lp_nonpreemptive_segment arr_seq j t1 := by
  intro huni hunit JLFP htrans arr_seq hva sched _ hwb hvs _ hvpm hvm hresp j ha hpos jlp hjlp hlp t1 t2
    hbip t hle
  have hcomp := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  rcases Nat.eq_zero_or_pos (service_during sched jlp t1 t) with hz | hsd
  · rw [hz]; exact Nat.zero_le _
  obtain ⟨st, hst, hs⟩ := cumulative_service_implies_scheduled sched jlp t1 t hsd
  have hst' := hst
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hst'
  have harr := low_priority_job_arrives_before_busy_interval_prefix arr_seq hva huni sched JLFP htrans hvpm
    hwb hvs hresp j ha hpos t1 t2 hbip jlp hlp st
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hs
  refine Nat.le_trans (lp_job_bounded_service (Task := Task) huni hunit JLFP htrans arr_seq hva sched hwb hvs
    hvpm hvm hresp j ha hpos jlp hjlp hlp t1 t2 hbip t hle) ?_
  unfold max_lp_nonpreemptive_segment arrivals_before
  refine si_le_bigMaxListCond _ _ (fun j_lp => job_max_nonpreemptive_segment j_lp - 1) jlp ?_ ?_
  · exact of_decide_eq_true (arrived_between_implies_in_arrivals arr_seq hva.1 jlp 0 t1 hjlp
      (by simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]; omega'))
  · have hc := scheduled_implies_positive_cost sched jlp hcomp st hs
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨hlp, hc⟩

/-- If the maximum lower-priority nonpreemptive segment is bounded by
`blocking_bound`, so is the service inversion of every job of `tsk`. -/
theorem service_inversion_is_bounded {Task : TaskType} [DecidableEq Task]
    [TaskMaxNonpreemptiveSegment Task] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    {PState : ProcessorState Job} :
    uniprocessor_model PState → unit_supply_proc_model PState →
    ∀ JLFP : JLFP_policy Job, reflexive_job_priorities JLFP → transitive_job_priorities JLFP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule PState) [JobReady Job PState], work_bearing_readiness arr_seq sched →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      respects_JLFP_policy_at_preemption_point arr_seq sched JLFP →
    ∀ (tsk : Task) (blocking_bound : duration → duration),
      (∀ (j : Job) (t1 t2 : instant), arrives_in arr_seq j → job_of_task tsk j = true →
        busy_interval_prefix arr_seq sched j t1 t2 →
        max_lp_nonpreemptive_segment arr_seq j t1 ≤ blocking_bound (job_arrival j - t1)) →
      service_inversion_is_bounded_by arr_seq sched tsk blocking_bound := by
  intro huni hunit JLFP hrefl htrans arr_seq hva sched _ hwb hvs _ hvpm hvm hresp tsk B hB
  have hfrom := hvs.1
  have hmust := valid_schedule_implies_jobs_must_arrive_to_execute sched arr_seq hvs
  unfold service_inversion_is_bounded_by pred_service_inversion_is_bounded_by
    pred_service_inversion_of_job_is_bounded_by
  intro j ha htsk hcost t1 t2 hbip
  have hpos : job_cost_positive j = true := by unfold job_cost_positive; exact decide_eq_true hcost
  refine Nat.le_trans ?_ (hB j t1 t2 ha htsk hbip)
  have hlt : t1 < t2 := hbip.1
  have hcsi_le := fun a b =>
    cumul_service_inv_le_cumul_priority_inv huni arr_seq hva sched hfrom hmust JLFP hrefl j a b
  rcases busy_interval_pi_cases arr_seq hva huni sched JLFP hrefl htrans hvpm hwb hvs hresp j ha hpos t1 t2
      hbip with hcpi | hpi
  · have := hcsi_le t1 t2
    rw [hcpi] at this
    change @cumulative_service_inversion Job _ PState arr_seq sched (JLFP_to_JLDP (JLFP := JLFP)) j t1 t2 ≤ _
    omega'
  · have hpi' := hpi
    unfold priority_inversion at hpi'
    simp only [Bool.and_eq_true, List.any_eq_true] at hpi'
    obtain ⟨_, jlp, hin, hlp⟩ := hpi'
    have hs1 : scheduled_at sched jlp t1 = true := by
      rw [← scheduled_jobs_at_iff arr_seq hva sched hfrom hmust jlp t1]; exact decide_eq_true hin
    have hjlp := hfrom jlp t1 hs1
    change @cumulative_service_inversion Job _ PState arr_seq sched (JLFP_to_JLDP (JLFP := JLFP)) j t1 t2 ≤ _
    rcases preemption_time_interval_case arr_seq sched t1 t2 with hnpt | ⟨pt, hpt, hPT, hmin⟩
    · refine Nat.le_trans (no_pt_si_bounded huni arr_seq hva sched hfrom hmust hvpm j jlp t1 t2 hnpt
        ⟨t1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega', hs1⟩) ?_
      exact lp_job_bounded_service_max (Task := Task) huni hunit JLFP htrans arr_seq hva sched hwb hvs hvpm hvm
        hresp j ha hpos jlp hjlp hlp t1 t2 hbip t2 (Nat.le_refl _)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at hpt
      have hcat := service_inversion_cat arr_seq sched (JLFP_to_JLDP (JLFP := JLFP)) j t1 t2 pt hpt.1
        (by omega')
      have hzero : cumulative_priority_inversion arr_seq sched j pt t2 = 0 := by
        unfold cumulative_priority_inversion
        apply Finset.sum_eq_zero
        intro x hx
        rw [Finset.mem_Ico] at hx
        have := no_priority_inversion_after_preemption_point arr_seq hva huni sched JLFP htrans hvpm hwb hvs
          hresp j ha hpos t1 t2 hbip pt hPT hpt.1 x
          (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true] at this
        rw [this]; rfl
      have h2 := hcsi_le pt t2
      rw [hzero] at h2
      have hpt1 : t1 < pt := by
        rcases Nat.lt_or_ge t1 pt with h | h
        · exact h
        · exfalso
          have heq : pt = t1 := by omega'
          subst heq
          have := no_preemption_time_before_pi arr_seq hva huni sched JLFP hrefl htrans hvpm hwb hvs hresp j
            ha hpos pt t2 hbip pt (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') hpi pt
            (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
          rw [hPT] at this
          exact absurd this (by decide)
      have hb := no_pt_si_bounded huni arr_seq hva sched hfrom hmust hvpm
        (JLDP := JLFP_to_JLDP (JLFP := JLFP)) j jlp t1 pt
        (fun x hx => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
          cases hx' : preemption_time arr_seq sched x
          · rfl
          · have := hmin x hx.1 hx'
            omega')
        ⟨t1, by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega', hs1⟩
      have hm := lp_job_bounded_service_max (Task := Task) huni hunit JLFP htrans arr_seq hva sched hwb hvs
        hvpm hvm hresp j ha hpos jlp hjlp hlp t1 t2 hbip pt (by omega')
      omega'

end ServiceInversion

end Prosa.Analysis.Facts.BusyInterval.ServiceInversion
