-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/facts/ideal_uni/preemption_aware.v

import Prosa.Implementation.Facts.GenericSchedule
import Prosa.Implementation.Definitions.IdealUniScheduler
import Prosa.Analysis.Facts.Model.Ideal.Schedule
import Prosa.Analysis.Facts.Readiness.Backlogged
import Prosa.Model.Schedule.LimitedPreemptive
import Prosa.Model.Schedule.PreemptionTime

namespace Prosa.Implementation.Facts.IdealUni.PreemptionAware

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Processor.Ideal
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Schedule.WorkConserving
open Prosa.Model.Schedule.LimitedPreemptive
open Prosa.Model.Schedule.PreemptionTime
open Prosa.Analysis.Definitions.SchedulePrefix
open Prosa.Analysis.Definitions.Readiness
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Service
open Prosa.Analysis.Facts.Readiness.Backlogged
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Implementation.Definitions.GenericScheduler
open Prosa.Implementation.Definitions.IdealUniScheduler
open Prosa.Implementation.Facts.GenericSchedule

/-! Properties of the preemption-model-aware ideal uniprocessor scheduler.
Binders follow the elaborated source types (each theorem takes only the
section inputs and hypotheses it uses, in their elaborated order; instance
inputs quantified after a hypothesis are `∀ [..]` binders). Representation:
the section-local `idle_state` is `none`; the section-local
`sched_prefix t`/`prefix t` (`if t is t'.+1 then schedule_up_to … t' else
empty_schedule …`) is inlined as a `match` on `t`, as in the elaborated types;
`j \in s` is `decide (j ∈ s) = true`; `x == Some j` is
`decide (x = some j) = true`; `choose_job t s = None <-> s = [::]` is an `↔`;
`t.+1`/`t.-1` are `t + 1`/`t - 1`. -/

section NPUniprocessorScheduler

variable {Job : JobType} [DecidableEq Job] [JobCost Job] [JobArrival Job]

/-! ### Local helpers (not source declarations) -/

/-- Deciding `s = some j` on an ideal state is deciding it on `Option Job`, as
in the accepted ideal-schedule facts. -/
local instance idealStateDecidableEqSome
    (s : (processor_state Job).State) (j : Job) : Decidable (s = some j) :=
  (inferInstance : DecidableEq (Option Job)) s (some j)

private theorem pmc_eq [JobReady Job (processor_state Job)] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (choose_job : instant → List Job → Option Job) (t : instant) :
    pmc_uni_schedule arr_seq choose_job t =
      allocation_at arr_seq choose_job
        (match t with
          | 0 => empty_schedule none
          | t' + 1 => schedule_up_to (allocation_at arr_seq choose_job) none t') t :=
  schedule_up_to_def (allocation_at arr_seq choose_job) none t

private theorem pmc_prefix [JobReady Job (processor_state Job)] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (choose_job : instant → List Job → Option Job) (h : instant) :
    identical_prefix (schedule_up_to (allocation_at arr_seq choose_job) none h)
      (pmc_uni_schedule arr_seq choose_job) (h + 1) :=
  schedule_up_to_identical_prefix (allocation_at arr_seq choose_job) none h (h + 1) (Nat.le_refl _)

private theorem alloc_zero [JobReady Job (processor_state Job)] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (choose_job : instant → List Job → Option Job)
    (sched : schedule (processor_state Job)) :
    allocation_at arr_seq choose_job sched 0 = choose_job 0 (jobs_backlogged_at arr_seq sched 0) := rfl

private theorem alloc_succ [JobReady Job (processor_state Job)] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (choose_job : instant → List Job → Option Job)
    (sched : schedule (processor_state Job)) (t : instant) :
    allocation_at arr_seq choose_job sched (t + 1) =
      bif prev_job_nonpreemptive sched (t + 1) then sched t
      else choose_job (t + 1) (jobs_backlogged_at arr_seq sched (t + 1)) := rfl

private theorem pmc_succ [JobReady Job (processor_state Job)] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (choose_job : instant → List Job → Option Job) (t : instant) :
    pmc_uni_schedule arr_seq choose_job (t + 1) =
      bif prev_job_nonpreemptive (schedule_up_to (allocation_at arr_seq choose_job) none t) (t + 1) then
        schedule_up_to (allocation_at arr_seq choose_job) none t t
      else choose_job (t + 1)
        (jobs_backlogged_at arr_seq (schedule_up_to (allocation_at arr_seq choose_job) none t) (t + 1)) :=
  pmc_eq arr_seq choose_job (t + 1)

private theorem sut_succ_self [JobReady Job (processor_state Job)] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (choose_job : instant → List Job → Option Job) (t : instant) :
    schedule_up_to (allocation_at arr_seq choose_job) none (t + 1) (t + 1) =
      bif prev_job_nonpreemptive (schedule_up_to (allocation_at arr_seq choose_job) none t) (t + 1) then
        schedule_up_to (allocation_at arr_seq choose_job) none t t
      else choose_job (t + 1)
        (jobs_backlogged_at arr_seq (schedule_up_to (allocation_at arr_seq choose_job) none t) (t + 1)) :=
  pmc_eq arr_seq choose_job (t + 1)

private theorem sut_widen [JobReady Job (processor_state Job)] [JobPreemptable Job]
    (arr_seq : arrival_sequence Job) (choose_job : instant → List Job → Option Job) (t : instant) :
    schedule_up_to (allocation_at arr_seq choose_job) none t t =
      schedule_up_to (allocation_at arr_seq choose_job) none (t + 1) t :=
  schedule_up_to_widen (allocation_at arr_seq choose_job) none t t (Nat.le_refl _)

private theorem prev_succ [JobReady Job (processor_state Job)] [JobPreemptable Job]
    (sched : schedule (processor_state Job)) (t : instant) :
    prev_job_nonpreemptive sched (t + 1) =
      match sched t with
      | some j => job_ready sched j (t + 1) && !job_preemptable j (service sched j (t + 1))
      | none => false := rfl

private theorem mem_backlogged_ready [JobReady Job (processor_state Job)]
    (arr_seq : arrival_sequence Job) (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    j ∈ jobs_backlogged_at arr_seq sched t → job_ready sched j t = true := by
  intro h
  unfold jobs_backlogged_at at h
  have hb := (List.mem_filter.mp h).2
  unfold backlogged at hb
  exact (Bool.and_eq_true_iff.mp hb).1

private theorem sched_some [JobReady Job (processor_state Job)]
    (sched : schedule (processor_state Job)) (j : Job) (t : instant) :
    scheduled_at sched j t = true ↔ sched t = some j := by
  rw [scheduled_at_def]; exact decide_eq_true_iff

/-! ### Work conservation -/

theorem allocation_at_idle (arr_seq : arrival_sequence Job) [RM : JobReady Job (processor_state Job)]
    [JobPreemptable Job] (choose_job : instant → List Job → Option Job) :
    (∀ (t : instant) (s : List Job), choose_job t s = none ↔ s = []) →
    ∀ (sched : schedule (processor_state Job)) (t : instant),
      allocation_at arr_seq choose_job sched t = none → jobs_backlogged_at arr_seq sched t = [] := by
  intro H_non_idling sched t
  cases t with
  | zero => intro h; exact (H_non_idling 0 _).mp h
  | succ t =>
      intro h
      rw [alloc_succ] at h
      cases hp : prev_job_nonpreemptive sched (t + 1) with
      | false => rw [hp] at h; exact (H_non_idling (t + 1) _).mp h
      | true =>
          rw [hp] at h
          have h' : sched t = none := h
          rw [prev_succ, h'] at hp
          exact absurd hp (by simp)

theorem idle_schedule_no_backlogged_jobs (arr_seq : arrival_sequence Job)
    [RM : JobReady Job (processor_state Job)] :
    nonclairvoyant_readiness RM →
    ∀ [JobPreemptable Job] (choose_job : instant → List Job → Option Job),
      (∀ (t : instant) (s : List Job), choose_job t s = none ↔ s = []) →
      ∀ t : instant, ideal_is_idle (pmc_uni_schedule arr_seq choose_job) t = true →
        jobs_backlogged_at arr_seq (pmc_uni_schedule arr_seq choose_job) t = [] := by
  intro H_nc _ choose_job H_non_idling t H_idle
  have NONE : pmc_uni_schedule arr_seq choose_job t = none := by
    unfold ideal_is_idle at H_idle
    cases hs : pmc_uni_schedule arr_seq choose_job t with
    | none => rfl
    | some _ => rw [hs] at H_idle; exact absurd H_idle (by simp)
  have IDLE := allocation_at_idle arr_seq choose_job H_non_idling _ t ((pmc_eq arr_seq choose_job t).symm.trans NONE)
  rw [← IDLE]
  refine backlogged_jobs_prefix_invariance H_nc arr_seq _ _ (t + 1) ?_ t (Nat.lt_succ_self t)
  intro x hx
  rcases Nat.lt_succ_iff_lt_or_eq.mp hx with LT | EQ
  · cases t with
    | zero => exact absurd LT (Nat.not_lt_zero _)
    | succ t' =>
        show schedule_up_to (allocation_at arr_seq choose_job) none x x =
          schedule_up_to (allocation_at arr_seq choose_job) none t' x
        exact schedule_up_to_prefix_inclusion _ _ x t' (Nat.le_of_lt_succ LT) x (Nat.le_refl _)
  · subst EQ
    rw [NONE]
    cases x with
    | zero => rfl
    | succ t' => exact (schedule_up_to_empty (allocation_at arr_seq choose_job) none t' (t' + 1) (Nat.lt_succ_self _)).symm

theorem np_schedule_work_conserving (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ [RM : JobReady Job (processor_state Job)], nonclairvoyant_readiness RM →
    ∀ [JobPreemptable Job] (choose_job : instant → List Job → Option Job),
      (∀ (t : instant) (s : List Job), choose_job t s = none ↔ s = []) →
      work_conserving arr_seq (pmc_uni_schedule arr_seq choose_job) := by
  intro H_valid RM H_nc _ choose_job H_non_idling j t ARRIVES BACKLOGGED
  rcases ideal_proc_model_sched_case_analysis Job (pmc_uni_schedule arr_seq choose_job) t with IDLE | SCHED
  · exfalso
    have NON_EMPTY := mem_backlogged_jobs arr_seq _ H_valid.1 j t ARRIVES BACKLOGGED
    rw [idle_schedule_no_backlogged_jobs arr_seq H_nc choose_job H_non_idling t IDLE] at NON_EMPTY
    exact absurd NON_EMPTY (by simp)
  · exact SCHED

/-! ### Validity -/

theorem np_schedule_jobs_from_arrival_sequence (arr_seq : arrival_sequence Job)
    [RM : JobReady Job (processor_state Job)] [JobPreemptable Job]
    (choose_job : instant → List Job → Option Job) :
    (∀ (t : instant) (s : List Job) (j : Job), choose_job t s = some j → decide (j ∈ s) = true) →
    jobs_come_from_arrival_sequence (pmc_uni_schedule arr_seq choose_job) arr_seq := by
  intro H_chooses j t SCHED
  rw [sched_some] at SCHED
  induction t with
  | zero =>
      rw [pmc_eq, alloc_zero] at SCHED
      exact backlogged_job_arrives_in arr_seq _ j 0 (H_chooses _ _ _ SCHED)
  | succ t IH =>
      rw [pmc_eq, alloc_succ] at SCHED
      cases hp : prev_job_nonpreemptive (schedule_up_to (allocation_at arr_seq choose_job) none t) (t + 1) with
      | true => rw [hp] at SCHED; exact IH SCHED
      | false =>
          rw [hp] at SCHED
          exact backlogged_job_arrives_in arr_seq _ j (t + 1) (H_chooses _ _ _ SCHED)

theorem chosen_job_is_ready (arr_seq : arrival_sequence Job)
    [RM : JobReady Job (processor_state Job)] [JobPreemptable Job]
    (choose_job : instant → List Job → Option Job) :
    (∀ (t : instant) (s : List Job) (j : Job), choose_job t s = some j → decide (j ∈ s) = true) →
    nonclairvoyant_readiness RM →
    ∀ (j : Job) (t : instant),
      decide (choose_job t (jobs_backlogged_at arr_seq
        (match t with
          | 0 => empty_schedule none
          | t' + 1 => schedule_up_to (allocation_at arr_seq choose_job) none t') t) = some j) = true →
      job_ready (pmc_uni_schedule arr_seq choose_job) j t = true := by
  intro H_chooses H_nc j t SCHED
  have IN := of_decide_eq_true (H_chooses _ _ _ (of_decide_eq_true SCHED))
  have READY := mem_backlogged_ready arr_seq _ j t IN
  rw [H_nc _ (pmc_uni_schedule arr_seq choose_job) j t ?_ t (Nat.le_refl _)] at READY
  · exact READY
  · intro x hx
    cases t with
    | zero => exact absurd hx (Nat.not_lt_zero _)
    | succ t' => exact pmc_prefix arr_seq choose_job t' x hx

theorem jobs_must_be_ready (arr_seq : arrival_sequence Job)
    [RM : JobReady Job (processor_state Job)] [JobPreemptable Job]
    (choose_job : instant → List Job → Option Job) :
    (∀ (t : instant) (s : List Job) (j : Job), choose_job t s = some j → decide (j ∈ s) = true) →
    nonclairvoyant_readiness RM →
    jobs_must_be_ready_to_execute (pmc_uni_schedule arr_seq choose_job) := by
  intro H_chooses H_nc j t SCHED
  rw [sched_some] at SCHED
  cases t with
  | zero =>
      rw [pmc_eq, alloc_zero] at SCHED
      exact chosen_job_is_ready arr_seq choose_job H_chooses H_nc j 0 (decide_eq_true SCHED)
  | succ t =>
      have E := pmc_succ arr_seq choose_job t
      cases hp : prev_job_nonpreemptive (schedule_up_to (allocation_at arr_seq choose_job) none t) (t + 1) with
      | false =>
          rw [hp] at E
          exact chosen_job_is_ready arr_seq choose_job H_chooses H_nc j (t + 1)
            (decide_eq_true (E.symm.trans SCHED))
      | true =>
          rw [hp] at E
          have S0 : schedule_up_to (allocation_at arr_seq choose_job) none t t = some j := E.symm.trans SCHED
          rw [prev_succ, S0] at hp
          have READY := (Bool.and_eq_true_iff.mp hp).1
          rw [H_nc _ (pmc_uni_schedule arr_seq choose_job) j (t + 1) (pmc_prefix arr_seq choose_job t)
            (t + 1) (Nat.le_refl _)] at READY
          exact READY

theorem np_schedule_valid (arr_seq : arrival_sequence Job)
    [RM : JobReady Job (processor_state Job)] [JobPreemptable Job]
    (choose_job : instant → List Job → Option Job) :
    (∀ (t : instant) (s : List Job) (j : Job), choose_job t s = some j → decide (j ∈ s) = true) →
    nonclairvoyant_readiness RM →
    valid_schedule (pmc_uni_schedule arr_seq choose_job) arr_seq :=
  fun H_chooses H_nc =>
    ⟨np_schedule_jobs_from_arrival_sequence arr_seq choose_job H_chooses,
      jobs_must_be_ready arr_seq choose_job H_chooses H_nc⟩

/-! ### Preemption times -/

theorem np_job_remains_scheduled (arr_seq : arrival_sequence Job)
    [RM : JobReady Job (processor_state Job)] [JobPreemptable Job]
    (choose_job : instant → List Job → Option Job) (t : Nat) :
    prev_job_nonpreemptive
        (match t with
          | 0 => empty_schedule none
          | t' + 1 => schedule_up_to (allocation_at arr_seq choose_job) none t') t = true →
      schedule_up_to (allocation_at arr_seq choose_job) none t t =
        schedule_up_to (allocation_at arr_seq choose_job) none t (t - 1) := by
  cases t with
  | zero => intro NP; exact absurd NP (by simp [prev_job_nonpreemptive])
  | succ t =>
      intro NP
      change prev_job_nonpreemptive (schedule_up_to (allocation_at arr_seq choose_job) none t) (t + 1) = true at NP
      have E := sut_succ_self arr_seq choose_job t
      rw [NP] at E
      rw [Nat.add_sub_cancel]
      exact E.trans (sut_widen arr_seq choose_job t)

theorem np_consistent (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ [RM : JobReady Job (processor_state Job)], nonclairvoyant_readiness RM →
    ∀ [JobPreemptable Job] (choose_job : instant → List Job → Option Job),
      (∀ (t : instant) (s : List Job) (j : Job), choose_job t s = some j → decide (j ∈ s) = true) →
      ∀ t : Nat,
        prev_job_nonpreemptive
            (match t with
              | 0 => empty_schedule none
              | t' + 1 => schedule_up_to (allocation_at arr_seq choose_job) none t') t = true →
          (!preemption_time arr_seq (pmc_uni_schedule arr_seq choose_job) t) = true := by
  intro H_valid RM H_nc _ choose_job H_chooses t NP
  have FROM := np_schedule_jobs_from_arrival_sequence arr_seq choose_job H_chooses
  have ARR := jobs_must_arrive_to_be_ready _ (jobs_must_be_ready arr_seq choose_job H_chooses H_nc)
  unfold preemption_time
  rw [scheduled_job_at_def Job arr_seq _ FROM ARR H_valid t]
  cases t with
  | zero => exact absurd NP (by simp [prev_job_nonpreemptive])
  | succ t =>
      have E := pmc_succ arr_seq choose_job t
      change prev_job_nonpreemptive (schedule_up_to (allocation_at arr_seq choose_job) none t) (t + 1) = true at NP
      rw [NP] at E
      have E' : pmc_uni_schedule arr_seq choose_job (t + 1) =
          schedule_up_to (allocation_at arr_seq choose_job) none t t := E
      rw [E']
      rw [prev_succ] at NP
      cases hs : schedule_up_to (allocation_at arr_seq choose_job) none t t with
      | none => rw [hs] at NP; exact absurd NP (by simp)
      | some j =>
          rw [hs] at NP
          have NPR := (Bool.and_eq_true_iff.mp NP).2
          show (!job_preemptable j (service (pmc_uni_schedule arr_seq choose_job) j (t + 1))) = true
          rw [← identical_prefix_service _ _ (t + 1) (pmc_prefix arr_seq choose_job t) j]
          exact NPR

/-! ### Preemption compliance -/

theorem np_respects_preemption_model (arr_seq : arrival_sequence Job)
    [RM : JobReady Job (processor_state Job)] :
    nonclairvoyant_readiness RM →
    ∀ [JobPreemptable Job] (choose_job : instant → List Job → Option Job),
      (∀ j : Job, arrives_in arr_seq j → job_cannot_become_nonpreemptive_before_execution j = true) →
      valid_nonpreemptive_readiness RM (pmc_uni_schedule arr_seq choose_job) →
      schedule_respects_preemption_model arr_seq (pmc_uni_schedule arr_seq choose_job) := by
  intro H_nc _ choose_job H_valid_pf H_valid_pb j t
  induction t with
  | zero =>
      intro ARR NP
      have H0 := H_valid_pf j ARR
      unfold job_cannot_become_nonpreemptive_before_execution at H0
      rw [service0] at NP
      rw [H0] at NP
      exact absurd NP (by simp)
  | succ t IH =>
      intro ARR NP
      have SCHED_t : scheduled_at (pmc_uni_schedule arr_seq choose_job) j t = true := by
        cases hs : scheduled_at (pmc_uni_schedule arr_seq choose_job) j t with
        | true => rfl
        | false =>
            have NO := not_scheduled_implies_no_service _ j t (by rw [hs]; rfl)
            rw [← service_last_plus_before, NO, Nat.add_zero] at NP
            have := IH ARR NP
            rw [hs] at this
            exact absurd this (by simp)
      rw [sched_some] at SCHED_t ⊢
      have SCHED : schedule_up_to (allocation_at arr_seq choose_job) none t t = some j := SCHED_t
      have PREFIX := pmc_prefix arr_seq choose_job t
      have NPP : prev_job_nonpreemptive (schedule_up_to (allocation_at arr_seq choose_job) none t) (t + 1) = true := by
        rw [prev_succ, SCHED]
        show (job_ready (schedule_up_to (allocation_at arr_seq choose_job) none t) j (t + 1) &&
          !job_preemptable j (service (schedule_up_to (allocation_at arr_seq choose_job) none t) j (t + 1))) = true
        rw [identical_prefix_service _ _ (t + 1) PREFIX j, NP, Bool.and_true,
          H_nc _ (pmc_uni_schedule arr_seq choose_job) j (t + 1) PREFIX (t + 1) (Nat.le_refl _)]
        exact H_valid_pb j (t + 1) NP
      have E := sut_succ_self arr_seq choose_job t
      rw [NPP] at E
      exact E.trans SCHED

end NPUniprocessorScheduler

end Prosa.Implementation.Facts.IdealUni.PreemptionAware
