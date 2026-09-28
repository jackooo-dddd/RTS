-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/priority/fifo.v

import Prosa.Model.Readiness.Basic
import Prosa.Model.Task.Sequentiality
import Prosa.Model.Priority.Fifo
import Prosa.Model.Schedule.WorkConserving
import Prosa.Analysis.Definitions.PriorityInversion
import Prosa.Analysis.Facts.Priority.Sequential
import Prosa.Analysis.Facts.Readiness.Basic
import Prosa.Analysis.Facts.BusyInterval.QuietTime
import Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
import Prosa.Analysis.Facts.Priority.Inversion
import Prosa.Analysis.Facts.BusyInterval.ServiceInversion

namespace Prosa.Analysis.Facts.Priority.Fifo

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Readiness.Basic
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Priority.Fifo
open Prosa.Model.Processor.PlatformProperties
open Prosa.Model.Schedule.Scheduled
open Prosa.Model.Schedule.WorkConserving
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.AlwaysHigherPriority
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.ServiceInversion.BusyPrefix
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Scheduled
open Prosa.Analysis.Facts.Priority.Sequential
open Prosa.Analysis.Facts.Priority.Inversion
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.BusyInterval.QuietTime
open Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
open Prosa.Analysis.Facts.BusyInterval.ServiceInversion
open Prosa.Util.Notation

/-! Facts about the FIFO policy.
Binders follow the elaborated source types. The `FIFO` policy is the accepted
global `FIFO` instance; where the source uses the JLDP view, it is the
accepted `JLFP_to_JLDP` of `FIFO`. The source's section-local
`basic_ready_instance` (implicit in the elaborated `valid_schedule` and
`work_conserving`) is the accepted Lean definition of the same name, passed
explicitly. Representation: a Boolean in `Prop` position is `= true`;
`~~ b` is `(!b) = true`; a Boolean equation `b = (x <= y)` is
`b = decide (x ≤ y)`. -/

section PriorityFacts

variable {Job : JobType} [DecidableEq Job]

/-- Under FIFO, `hep_job` compares arrival times. -/
theorem hep_job_arrival_FIFO [JobArrival Job] :
    ∀ j j' : Job, (FIFO Job).hep_job j j' = decide (job_arrival j ≤ job_arrival j') :=
  fun _ _ => rfl

/-- Under FIFO, `~~ hep_job` is a strict inequality of arrival times. -/
theorem not_hep_job_arrival_FIFO [JobArrival Job] :
    ∀ j j' : Job, (!(FIFO Job).hep_job j j') = decide (job_arrival j' < job_arrival j) := by
  intro j j'
  rw [hep_job_arrival_FIFO]
  by_cases h : job_arrival j ≤ job_arrival j'
  · rw [decide_eq_true h, decide_eq_false (by omega')]; rfl
  · rw [decide_eq_false h, decide_eq_true (by omega')]; rfl

/-- Under FIFO, `~~ hep_job j j'` implies `hep_job j' j`. -/
theorem not_hep_job_FIFO [JobArrival Job] :
    ∀ j j' : Job, (!(FIFO Job).hep_job j j') = true → (FIFO Job).hep_job j' j = true := by
  intro j j' h
  rw [not_hep_job_arrival_FIFO] at h
  rw [hep_job_arrival_FIFO]
  have := of_decide_eq_true h
  exact decide_eq_true (by omega')

/-- Under FIFO, `~~ hep_job j j'` implies that `j'` always has higher
priority. -/
theorem not_hep_job_always_higher_priority_FIFO [JobArrival Job] :
    ∀ j j' : Job, (!(FIFO Job).hep_job j j') = true →
      @always_higher_priority Job _ (JLFP_to_JLDP (JLFP := FIFO Job)) j' j := by
  intro j j' h
  refine (@always_higher_priority_jlfp Job _ (FIFO Job) j' j).2 ?_
  simp only [Bool.and_eq_true]
  exact ⟨not_hep_job_FIFO j j' h, h⟩

end PriorityFacts

section BasicLemmas

variable {Job : JobType} [DecidableEq Job]

/-- LEAN_HELPER: the scheduled-jobs view of `must_arrive` from a basic-valid
schedule. -/
private theorem basic_valid_must_arrive [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    {PState : ProcessorState Job} (sched : schedule PState)
    (hvs : @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq) :
    jobs_must_arrive_to_execute sched := by
  intro j t hs
  have h : pending sched j t = true := hvs.2 j t hs
  unfold pending at h
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- LEAN_HELPER: a FIFO priority inversion exhibits a scheduled job of lower
priority. -/
private theorem fifo_pi_witness [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) {PState : ProcessorState Job}
    (huni : uniprocessor_model PState) (sched : schedule PState)
    (hfrom : jobs_come_from_arrival_sequence sched arr_seq) (hmust : jobs_must_arrive_to_execute sched)
    (j : Job) (t : instant) (hpi : @priority_inversion Job _ PState arr_seq sched (FIFO Job) j t = true) :
    ∃ j' : Job, scheduled_at sched j' t = true ∧ (!(FIFO Job).hep_job j' j) = true := by
  have hr := uni_priority_inversion_P arr_seq hva sched hfrom hmust (JLFP := FIFO Job) FIFO_is_reflexive j
    huni t
  rw [hpi] at hr
  cases hr with
  | isTrue hx => exact hx

/-- LEAN_HELPER: `j1` arriving before `j2` is always of higher FIFO priority. -/
private theorem fifo_always_higher [JobArrival Job] (j1 j2 : Job)
    (h : job_arrival j1 < job_arrival j2) :
    @always_higher_priority Job _ (JLFP_to_JLDP (JLFP := FIFO Job)) j1 j2 :=
  not_hep_job_always_higher_priority_FIFO j2 j1 (by rw [not_hep_job_arrival_FIFO]; exact decide_eq_true h)

/-- LEAN_HELPER: under FIFO, a job arriving earlier than a scheduled job is
complete. -/
private theorem fifo_early_completed [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job)
    (hva : valid_arrival_sequence arr_seq) {PState : ProcessorState Job}
    (huni : uniprocessor_model PState) (sched : schedule PState)
    (hvs : @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq) [JobPreemptable Job]
    (hvpm : valid_preemption_model arr_seq sched)
    (hresp : @respects_JLFP_policy_at_preemption_point Job _ _ _ PState _ basic_ready_instance arr_seq sched (FIFO Job))
    (j1 j2 : Job) (ha : arrives_in arr_seq j1) (hlt : job_arrival j1 < job_arrival j2) (t : instant)
    (hs : scheduled_at sched j2 t = true) : completed_by sched j1 t = true := by
  letI : JobReady Job PState := basic_ready_instance
  exact early_hep_job_is_scheduled arr_seq hva (FIFO Job) FIFO_is_transitive PState huni sched
    (basic_readiness_is_work_bearing_readiness arr_seq sched FIFO_is_reflexive) hvs hvpm hresp j1 j2 ha
    hlt (fifo_always_higher j1 j2 hlt) t hs

/-- A FIFO schedule has no priority inversion. -/
theorem FIFO_implies_no_priority_inversion [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState, @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ PState _ basic_ready_instance arr_seq sched (FIFO Job) →
    ∀ (j : Job) (t : instant), arrives_in arr_seq j → pending sched j t = true →
      (!@priority_inversion Job _ PState arr_seq sched (FIFO Job) j t) = true := by
  intro hva PState huni sched hvs _ hvpm hresp j t ha hpend
  cases hpi : @priority_inversion Job _ PState arr_seq sched (FIFO Job) j t
  · rfl
  · exfalso
    have hfrom := hvs.1
    have hmust := basic_valid_must_arrive arr_seq sched hvs
    obtain ⟨j', hs', hnhep⟩ := fifo_pi_witness arr_seq hva huni sched hfrom hmust j t hpi
    rw [not_hep_job_arrival_FIFO] at hnhep
    have hc := fifo_early_completed arr_seq hva huni sched hvs hvpm hresp j j' ha
      (of_decide_eq_true hnhep) t hs'
    unfold pending at hpend
    rw [hc] at hpend
    simp at hpend

/-- In a FIFO schedule, all jobs of higher priority than a scheduled job are
complete. -/
theorem scheduled_implies_higher_priority_completed [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState, @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ PState _ basic_ready_instance arr_seq sched (FIFO Job) →
    ∀ (j : Job) (t : instant), scheduled_at sched j t = true →
    ∀ j_hp : Job, arrives_in arr_seq j_hp → (!(FIFO Job).hep_job j j_hp) = true →
      completed_by sched j_hp t = true := by
  intro hva PState huni sched hvs _ hvpm hresp j t hs j_hp ha hn
  rw [not_hep_job_arrival_FIFO] at hn
  exact fifo_early_completed arr_seq hva huni sched hvs hvpm hresp j_hp j ha (of_decide_eq_true hn) t hs

/-- FIFO bounds priority inversion by zero. -/
theorem FIFO_implies_no_pi [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState, @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ PState _ basic_ready_instance arr_seq sched (FIFO Job) →
    ∀ {Task : TaskType} [DecidableEq Task] [JobTask Job Task] (tsk : Task),
      @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ PState arr_seq sched (FIFO Job) tsk
        (constant 0) := by
  intro hva PState huni sched hvs _ hvpm hresp Task _ _ tsk _ j ha _ hpos t1 t2 hbip
  have hfrom := hvs.1
  have hmust := basic_valid_must_arrive arr_seq sched hvs
  show _ ≤ 0
  apply Nat.le_of_eq
  unfold cumulative_priority_inversion
  apply Finset.sum_eq_zero
  intro t ht
  rw [Finset.mem_Ico] at ht
  cases hpi : @priority_inversion Job _ PState arr_seq sched (FIFO Job) j t
  · rfl
  · exfalso
    obtain ⟨j', hs', hnhep⟩ := fifo_pi_witness arr_seq hva huni sched hfrom hmust j t hpi
    have hstart := hbip.2.2.2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hstart
    rcases Nat.eq_or_lt_of_le ht.1 with heq | hgt
    · subst heq
      have hc := scheduled_implies_higher_priority_completed arr_seq hva PState huni sched hvs hvpm hresp
        j' t1 hs' j ha (by rw [not_hep_job_arrival_FIFO] at hnhep ⊢; exact hnhep)
      obtain ⟨t', ht', _⟩ := completed_implies_scheduled_before sched j hpos hmust t1 hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at ht'
      omega'
    · apply busy_interval_prefix_no_quiet_time sched arr_seq j t1 t2 hbip t
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hgt, ht.2⟩)
      intro jhp hjhp hhep _
      apply scheduled_implies_higher_priority_completed arr_seq hva PState huni sched hvs hvpm hresp j' t
        hs' jhp hjhp
      rw [not_hep_job_arrival_FIFO] at hnhep ⊢
      rw [hep_job_arrival_FIFO] at hhep
      have h1 := of_decide_eq_true hnhep
      have h2 := of_decide_eq_true hhep
      exact decide_eq_true (by omega')

/-- FIFO bounds service inversion by zero. -/
theorem FIFO_implies_no_service_inversion [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState, @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ PState _ basic_ready_instance arr_seq sched (FIFO Job) →
    ∀ {Task : TaskType} [DecidableEq Task] [JobTask Job Task] (tsk : Task),
      @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
      @service_inversion_is_bounded_by Task _ Job _ _ _ _ PState arr_seq sched (FIFO Job) tsk
        (constant 0) := by
  intro hva PState huni sched hvs _ hvpm hresp Task _ _ tsk hvs' j ha htsk hpos t1 t2 hbip
  have hfrom := hvs.1
  have hmust := basic_valid_must_arrive arr_seq sched hvs
  have hle := cumul_service_inv_le_cumul_priority_inv huni arr_seq hva sched hfrom hmust (FIFO Job)
    FIFO_is_reflexive j t1 t2
  have hpi := FIFO_implies_no_pi arr_seq hva PState huni sched hvs hvpm hresp tsk hvs' j ha htsk hpos t1 t2
    hbip
  exact Nat.le_trans hle hpi

/-- Tasks execute sequentially in a FIFO schedule. -/
theorem tasks_execute_sequentially [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState, @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ PState _ basic_ready_instance arr_seq sched (FIFO Job) →
    ∀ {Task : TaskType} [DecidableEq Task] [JobTask Job Task],
      sequential_tasks (Task := Task) arr_seq sched := by
  intro hva PState huni sched hvs _ hvpm hresp Task _ _ j1 j2 t ha1 _ _ hlt hs
  exact fifo_early_completed arr_seq hva huni sched hvs hvpm hresp j1 j2 ha1 hlt t hs

/-- FIFO respects the sequential-tasks hypothesis. -/
theorem fifo_respects_sequential_tasks [JobArrival Job] {Task : TaskType} [DecidableEq Task]
    [JobTask Job Task] :
    policy_respects_sequential_tasks (Task := Task) (FIFO Job) := by
  intro j1 j2 _ hle
  rw [hep_job_arrival_FIFO]
  exact decide_eq_true hle

/-- Without superfluous preemptions, a FIFO schedule has no preemptions. -/
theorem no_preemptions_under_FIFO [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState, @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
      @work_conserving Job _ _ _ PState basic_ready_instance arr_seq sched →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ PState _ basic_ready_instance arr_seq sched (FIFO Job) →
      @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := FIFO Job)) PState sched →
    ∀ (j : Job) (t : instant), (!preempted_at sched j t) = true := by
  intro hva PState huni sched hvs hwc _ hvpm hresp hnsp j t
  have hfrom := hvs.1
  have hmust := basic_valid_must_arrive arr_seq sched hvs
  cases hp : preempted_at sched j t
  · rfl
  · exfalso
    have hp' := hp
    unfold preempted_at at hp'
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp'
    obtain ⟨⟨hs1, hnc⟩, hns⟩ := hp'
    cases hsj : scheduled_job_at arr_seq sched t with
    | some j' =>
      have hs' : scheduled_at sched j' t = true :=
        (scheduled_job_at_scheduled_at arr_seq hva sched hfrom hmust huni j' t).symm.trans
          (decide_eq_true hsj)
      have hn := hnsp t j j' hp hs'
      have hlt : job_arrival j' < job_arrival j := by
        have := hn
        change (!(FIFO Job).hep_job j j') = true at this
        rw [not_hep_job_arrival_FIFO] at this
        exact of_decide_eq_true this
      have hc := fifo_early_completed arr_seq hva huni sched hvs hvpm hresp j' j (hfrom j' t hs') hlt (t - 1)
        hs1
      have hnc' := scheduled_implies_not_completed sched j'
        (fun x y h => by
          have hp2 : pending sched x y = true := hvs.2 x y h
          unfold pending completed_by at hp2
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hp2
          omega') t hs'
      have hnc'' := incompletion_monotonic sched j' (t - 1) t (Nat.sub_le t 1) hnc'
      rw [hc] at hnc''
      exact absurd hnc'' (by decide)
    | none =>
      have hall := (scheduled_job_at_none arr_seq hva sched hfrom hmust t).1 hsj
      obtain ⟨j', hs'⟩ := hwc j t (hfrom j (t - 1) hs1) (by
        unfold backlogged
        simp only [Bool.and_eq_true]
        refine ⟨?_, by rw [hns]; rfl⟩
        show pending sched j t = true
        unfold pending
        simp only [Bool.and_eq_true]
        refine ⟨?_, by rw [hnc]; rfl⟩
        have := hmust j (t - 1) hs1
        unfold has_arrived at this ⊢
        have h1 := of_decide_eq_true this
        exact decide_eq_true (by omega')
        )
      have := hall j'
      rw [hs'] at this
      exact absurd this (by decide)

/-- Hence a FIFO schedule is nonpreemptive. -/
theorem FIFO_is_nonpreemptive [JobArrival Job] [JobCost Job] (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ PState : ProcessorState Job, uniprocessor_model PState →
    ∀ sched : schedule PState, @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq →
      @work_conserving Job _ _ _ PState basic_ready_instance arr_seq sched →
    ∀ [JobPreemptable Job], valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ PState _ basic_ready_instance arr_seq sched (FIFO Job) →
      @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := FIFO Job)) PState sched →
      nonpreemptive_schedule sched := by
  intro hva PState huni sched hvs hwc _ hvpm hresp hnsp
  exact (no_preemptions_equiv_nonpreemptive sched).1
    (no_preemptions_under_FIFO arr_seq hva PState huni sched hvs hwc hvpm hresp hnsp)

end BasicLemmas

end Prosa.Analysis.Facts.Priority.Fifo
