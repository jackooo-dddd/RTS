-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/busy_interval.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 102)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions

/-!
Busy intervals for JLFP-models (Rocq module `BusyIntervalJLFP`).

Representation notes:
* `work_conserving` is `LimitedPreemptionPlatform.work_conserving` (the `Import`ed one), which unfolds to the basic
  platform's work conservation.
* Boolean tests in proposition position are `= true`; `~~ b` is `!b`; `a ==> b` is `!a || b`; Boolean chains
  `a < x < b`, `a <= x < b`, `a < x <= b` in proposition position are `(decide (…) && decide (…)) = true`;
  `if sched t is Some jlp then … else false` is a `match`; a Boolean summed as a number is `Bool.toNat`;
  `\sum_(t1 <= t < t2)` is `∑ t ∈ Finset.Ico t1 t2`; `predT` is `fun _ => true`; `t.+1` is `t + 1`.
* `reflect (quiet_time j t) (quiet_time_dec j t)` is the informative `BoolReflect`, so `quiet_time_P` is a `def`.
* The section-local `Let`s (`job_pending_at`, `job_scheduled_at`, `job_completed_by`, `job_remaining_cost`,
  `arrivals_between`, `quiet_time`, `busy_interval_prefix`, `busy_interval`, `is_priority_inversion_bounded_by`,
  `service_received_by_hep_jobs_released_during`, `hp_workload`, `hp_service`, `total_workload`,
  `total_service`) are unfolded.
* As in the source, `job_completes_within_busy_interval` assumes `FP_is_reflexive higher_eq_priority` (for the JLFP
  relation viewed as an FP relation over jobs).
* Binder lists follow the Rocq contract.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Schedule.Uni.Service.Service
open Prosa.Classic.Model.Schedule.Uni.Workload.Workload
open Prosa.Classic.Util.List (BoolReflect)
open Prosa.Util.Sum (sumFiltered ltn_sum_leq_seq)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def quiet_time {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (t : time) : Prop :=
  ∀ j_hp, arrives_in arr_seq j_hp → higher_eq_priority j_hp j = true →
    arrived_before job_arrival j_hp t = true → completed_by job_cost sched j_hp t = true

def busy_interval_prefix {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t_busy : time) : Prop :=
  t1 < t_busy ∧ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t1 ∧
  (∀ t, (decide (t1 < t) && decide (t < t_busy)) = true → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) ∧
  (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t_busy)) = true

def busy_interval {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t2 : time) : Prop :=
  busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 ∧ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t2

def is_priority_inversion {Job : Type v} [DecidableEq Job] (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (t : time) : Bool :=
  match sched t with
  | some jlp => !higher_eq_priority jlp j
  | none => false

def cumulative_priority_inversion {Job : Type v} [DecidableEq Job] (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (is_priority_inversion sched higher_eq_priority j t).toNat

def priority_inversion_of_job_is_bounded_by {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (B : time) : Prop :=
  ∀ t1 t2 : time, busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 → cumulative_priority_inversion sched higher_eq_priority j t1 t2 ≤ B

def priority_inversion_is_bounded_by {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (tsk : Task)
    (B : time) : Prop :=
  ∀ j : Job, arrives_in arr_seq j → job_task j = tsk → 0 < job_cost j →
    priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j B

def quiet_time_dec {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job)
    (j : Job) (t : time) : Bool :=
  (jobs_arrived_before arr_seq t).all (fun j_hp => !higher_eq_priority j_hp j || completed_by job_cost sched j_hp t)

/-- LEAN_HELPER: `quiet_time_dec` decides `quiet_time`. -/
private theorem quiet_time_iff {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (t : time) :
    quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t ↔ quiet_time_dec job_cost arr_seq sched higher_eq_priority j t = true := by
  unfold quiet_time quiet_time_dec
  rw [List.all_eq_true]
  constructor
  · intro QT s INs
    have ARRs := in_arrivals_implies_arrived arr_seq s 0 t INs
    have BEF := in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent s t INs
    cases hs : higher_eq_priority s j
    · simp
    · simp [QT s ARRs hs BEF]
  · intro ALL s ARRs HPs BEFs
    have INs : s ∈ jobs_arrived_before arr_seq t := by
      unfold jobs_arrived_before
      apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent s 0 t ARRs
      simp only [arrived_before, decide_eq_true_eq] at BEFs
      simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨Nat.zero_le _, BEFs⟩
    have := ALL s INs
    simpa [HPs] using this

def quiet_time_P {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) :
    ∀ (j : Job) (t : time),
      BoolReflect (quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) (quiet_time_dec job_cost arr_seq sched higher_eq_priority j t) := by
  intro j t
  cases h : quiet_time_dec job_cost arr_seq sched higher_eq_priority j t
  · exact BoolReflect.isFalse (fun QT => by
      rw [(quiet_time_iff job_arrival job_cost arr_seq H_arrival_times_are_consistent sched higher_eq_priority j t).mp
        QT] at h
      exact Bool.noConfusion h)
  · exact BoolReflect.isTrue
      ((quiet_time_iff job_arrival job_cost arr_seq H_arrival_times_are_consistent sched higher_eq_priority j t).mpr h)

theorem job_completes_within_busy_interval {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j) (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (t1 t2 : time) (H_busy_interval : busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2) :
    completed_by job_cost sched j t2 = true := by
  obtain ⟨⟨_, _, _, ARR⟩, QUIET⟩ := H_busy_interval
  simp only [Bool.and_eq_true] at ARR
  exact QUIET j H_from_arrival_sequence (H_priority_is_reflexive j)
    (by simp only [arrived_before]; exact decide_eq_true (of_decide_eq_true ARR.2))

theorem not_quiet_implies_exists_pending_job {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t2 : time)
    (H_interval : t1 ≤ t2) (H_quiet : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t1) (H_not_quiet : ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t2) :
    ∃ j_hp, arrives_in arr_seq j_hp ∧ arrived_between job_arrival j_hp t1 t2 = true ∧
      higher_eq_priority j_hp j = true ∧ ¬ (completed_by job_cost sched j_hp t2 = true) := by
  by_contra NONE
  push_neg at NONE
  apply H_not_quiet
  intro j_hp IN HPj ARR
  have ARR' := of_decide_eq_true ARR
  by_cases h : job_arrival j_hp < t1
  · exact completion_monotonic job_cost sched j_hp t1 t2 H_interval
      (H_quiet j_hp IN HPj (decide_eq_true h))
  · exact NONE j_hp IN (by simp only [arrived_between, Bool.and_eq_true]; exact ⟨decide_eq_true (by omega'),
      decide_eq_true ARR'⟩) HPj

theorem idle_time_implies_quiet_time_at_the_next_time_instant {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) :
    ∀ t : time, is_idle sched t = true → quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j (t + 1) := by
  intro t IDLE jhp ARR HPj AB
  have AB' := of_decide_eq_true AB
  have IDLE' := of_decide_eq_true IDLE
  cases hc : completed_by job_cost sched jhp (t + 1)
  · exfalso
    have NC : completed_by job_cost sched jhp t = false := by
      cases hct : completed_by job_cost sched jhp t
      · rfl
      · have := completion_monotonic job_cost sched jhp t (t + 1) (Nat.le_succ _) hct
        rw [hc] at this; exact Bool.noConfusion this
    have BACK : backlogged job_arrival job_cost sched jhp t = true := by
      have hA : has_arrived job_arrival jhp t = true := decide_eq_true (by omega')
      have hS : scheduled_at sched jhp t = false := by simp [scheduled_at, IDLE']
      simp [backlogged, pending, hA, NC, hS]
    obtain ⟨jo, SCHED⟩ := H_work_conserving jhp t ARR BACK
    simp [scheduled_at, IDLE'] at SCHED
  · rfl

theorem pending_hp_job_exists {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (t1 t2 : time) (H_busy_interval_prefix : busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2) :
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
      ∃ jhp, arrives_in arr_seq jhp ∧ pending job_arrival job_cost sched jhp t = true ∧
        higher_eq_priority jhp j = true := by
  intro t H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  obtain ⟨_, _, NQT, REL⟩ := H_busy_interval_prefix
  -- a non-quiet instant `s` with `t ≤ s` provides a pending higher-or-equal-priority job at `t`
  have FROM_NQ : ∀ s, t < s + 1 → s ≤ t + 1 → (decide (t1 < s) && decide (s < t2)) = true →
      ∃ jhp, arrives_in arr_seq jhp ∧ pending job_arrival job_cost sched jhp t = true ∧
        higher_eq_priority jhp j = true := by
    intro s h1 h2 hs
    have NQ := NQT s hs
    unfold quiet_time at NQ
    push_neg at NQ
    obtain ⟨jhp, ARR, HPj, BEF, NCOMP⟩ := NQ
    have BEF' := of_decide_eq_true BEF
    refine ⟨jhp, ARR, ?_, HPj⟩
    simp only [pending, has_arrived, Bool.and_eq_true, Bool.not_eq_true']
    refine ⟨decide_eq_true (by omega'), ?_⟩
    cases hc : completed_by job_cost sched jhp t
    · rfl
    · exact absurd (completion_monotonic job_cost sched jhp t s (by omega') hc) NCOMP
  rcases Nat.lt_or_ge t1 t with LT | GE
  · exact FROM_NQ t (by omega') (by omega')
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
  · have EQ : t = t1 := by omega'
    subst EQ
    by_cases h2 : t + 1 < t2
    · exact FROM_NQ (t + 1) (by omega') (Nat.le_refl _)
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
    · simp only [Bool.and_eq_true] at REL
      have A1 := of_decide_eq_true REL.1
      have A2 := of_decide_eq_true REL.2
      have EQa : job_arrival j = t := by omega'
      refine ⟨j, H_from_arrival_sequence, ?_, H_priority_is_reflexive j⟩
      rw [← EQa]
      exact job_pending_at_arrival job_arrival job_cost sched H_jobs_must_arrive_to_execute j arr_seq
        H_from_arrival_sequence (of_decide_eq_true H_job_cost_positive)

theorem not_quiet_implies_not_idle {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j) (H_job_cost_positive : job_cost_positive job_cost j = true)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (t1 t2 : time) (H_busy_interval_prefix : busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2) :
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true → ¬ (is_idle sched t = true) := by
  intro t NEQ IDLE
  obtain ⟨jhp, ARR, PEND, _⟩ := pending_hp_job_exists job_arrival job_cost arr_seq H_arrival_times_are_consistent
    sched higher_eq_priority j H_from_arrival_sequence H_job_cost_positive H_jobs_must_arrive_to_execute
    H_priority_is_reflexive t1 t2 H_busy_interval_prefix t NEQ
  have IDLE' := of_decide_eq_true IDLE
  have BACK : backlogged job_arrival job_cost sched jhp t = true := by
    simp [backlogged, PEND, scheduled_at, IDLE']
  obtain ⟨jo, SCHED⟩ := H_work_conserving jhp t ARR BACK
  simp [scheduled_at, IDLE'] at SCHED

/-! ### Proof-local facts about filtered sums -/

private theorem sumFiltered_exchange {I : Type _} (l : List I) (P : I → Bool) (f : I → Nat → Nat) (t1 t2 : Nat) :
    sumFiltered l P (fun i => ∑ t ∈ Finset.Ico t1 t2, f i t) =
      ∑ t ∈ Finset.Ico t1 t2, sumFiltered l P (fun i => f i t) := by
  unfold sumFiltered
  induction (l.filter P) with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

private theorem sumFiltered_split {I : Type _} (l : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered l (fun _ => true) F = sumFiltered l P F + sumFiltered l (fun i => !P i) F := by
  unfold sumFiltered
  induction l with
  | nil => simp
  | cons a l ih =>
    cases h : P a <;> simp [List.filter_cons, h] at ih ⊢ <;> omega

private theorem sumFiltered_append {I : Type _} (l1 l2 : List I) (P : I → Bool) (F : I → Nat) :
    sumFiltered (l1 ++ l2) P F = sumFiltered l1 P F + sumFiltered l2 P F := by
  simp [sumFiltered, List.filter_append]

private theorem sumFiltered_zero {I : Type _} (l : List I) (P : I → Bool) (F : I → Nat)
    (h : ∀ i ∈ l, P i = true → F i = 0) : sumFiltered l P F = 0 := by
  unfold sumFiltered
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  rw [List.mem_filter] at hi
  exact h i hi.1 hi.2

theorem hep_jobs_receive_no_service_before_quiet_time {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (t1 : time) (H_quiet_time : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t1) (Δ : time) :
    service_of_higher_or_equal_priority_jobs sched (jobs_arrived_between arr_seq t1 (t1 + Δ)) higher_eq_priority j t1
        (t1 + Δ) =
      service_of_higher_or_equal_priority_jobs sched (jobs_arrived_between arr_seq 0 (t1 + Δ)) higher_eq_priority j t1
        (t1 + Δ) := by
  unfold service_of_higher_or_equal_priority_jobs service_of_jobs
  rw [job_arrived_between_cat arr_seq 0 t1 (t1 + Δ) (Nat.zero_le _) (Nat.le_add_right _ _), sumFiltered_append]
  have Z : sumFiltered (jobs_arrived_between arr_seq 0 t1) (fun j_hp => higher_eq_priority j_hp j)
      (fun j' => service_during sched j' t1 (t1 + Δ)) = 0 := by
    apply sumFiltered_zero
    intro jhp IN HPj
    have ARR := in_arrivals_implies_arrived arr_seq jhp 0 t1 IN
    have BEF := in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent jhp t1 IN
    have C := H_quiet_time jhp ARR HPj BEF
    unfold service_during
    apply Finset.sum_eq_zero
    intro t' ht'
    rw [Finset.mem_Ico] at ht'
    have C' := completion_monotonic job_cost sched jhp t1 t' ht'.1 C
    have NS := completed_implies_not_scheduled job_cost sched jhp H_completed_jobs_dont_execute t' C'
    simp only [Bool.not_eq_true'] at NS
    simp [service_at, NS]
  rw [Z, Nat.zero_add]

theorem no_idle_time_within_non_quiet_time_interval {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (t1 Δ : time)
    (H_no_quiet_time : ∀ t, (decide (t1 < t) && decide (t ≤ t1 + Δ)) = true → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) :
    service_of_jobs sched (jobs_arrived_between arr_seq 0 (t1 + Δ)) (fun _ => true) t1 (t1 + Δ) = Δ := by
  unfold service_of_jobs service_during
  rw [sumFiltered_exchange]
  calc _ = ∑ _x ∈ Finset.Ico t1 (t1 + Δ), (1 : Nat) := by
        apply Finset.sum_congr rfl
        intro t' ht'
        rw [Finset.mem_Ico] at ht'
        apply Nat.le_antisymm
        · exact service_of_jobs_le_1 job_arrival arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
            sched 0 (t1 + Δ) t' (fun _ => true)
        · cases SCHED : sched t' with
          | none =>
            exfalso
            have IDLE : is_idle sched t' = true := by simp [is_idle, SCHED]
            rcases Nat.eq_or_lt_of_le ht'.1 with EQ | LT
            · subst EQ
              exact H_no_quiet_time (t1 + 1) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
                (idle_time_implies_quiet_time_at_the_next_time_instant job_arrival job_cost arr_seq sched
                  higher_eq_priority j H_work_conserving t1 IDLE)
            · apply H_no_quiet_time t' (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
              intro j_hp IN HPj ARR
              have ARR' := of_decide_eq_true ARR
              cases hc : completed_by job_cost sched j_hp t'
              · exfalso
                have BACK : backlogged job_arrival job_cost sched j_hp t' = true := by
                  have hA : has_arrived job_arrival j_hp t' = true := decide_eq_true (by omega')
                  have hS : scheduled_at sched j_hp t' = false := by simp [scheduled_at, SCHED]
                  simp [backlogged, pending, hA, hc, hS]
                obtain ⟨jo, SCHo⟩ := H_work_conserving j_hp t' IN BACK
                simp [scheduled_at, SCHED] at SCHo
              · rfl
          | some j1 =>
            have SCH1 : scheduled_at sched j1 t' = true := by simp [scheduled_at, SCHED]
            have ARRj1 := H_jobs_come_from_arrival_sequence j1 t' SCH1
            have HA := of_decide_eq_true (H_jobs_must_arrive_to_execute j1 t' SCH1)
            have IN : j1 ∈ jobs_arrived_between arr_seq 0 (t1 + Δ) :=
              arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j1 0 (t1 + Δ)
                ARRj1 (by simp only [arrived_between, Bool.and_eq_true]; exact ⟨decide_eq_true (Nat.zero_le _),
                  decide_eq_true (by omega')⟩)
            have h1 : service_at sched j1 t' = 1 := by simp [service_at, SCH1]
            have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun i => service_at sched i t')
              ((List.mem_filter (p := fun _ => true)).mpr ⟨IN, rfl⟩))
            unfold sumFiltered; omega'
    _ = Δ := by simp

theorem exists_busy_interval_prefix {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j) (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (t_busy : time)
    (H_j_is_pending : pending job_arrival job_cost sched j t_busy = true) :
    ∃ t1, busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 (t_busy + 1) ∧
      (decide (t1 ≤ job_arrival j) && decide (job_arrival j ≤ t_busy)) = true := by
  classical
  have Q0 : quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j 0 := by intro j_hp _ _ ARR; simp [arrived_before] at ARR
  have SPEC := Nat.findGreatest_spec (P := fun t => quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) (Nat.zero_le t_busy) Q0
  have LE := Nat.findGreatest_le (P := fun t => quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) t_busy
  have GREAT : ∀ k, Nat.findGreatest (fun t => quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) t_busy < k → k ≤ t_busy → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j k :=
    fun k h hk => Nat.findGreatest_is_greatest h hk
  generalize Nat.findGreatest (fun t => quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) t_busy = last at SPEC LE GREAT
  have PEND := H_j_is_pending
  simp only [pending, Bool.and_eq_true, Bool.not_eq_true'] at PEND
  have ARRj := of_decide_eq_true PEND.1
  have JA : last ≤ job_arrival j := by
    by_contra hc
    have C1 := SPEC j H_from_arrival_sequence (H_priority_is_reflexive j) (decide_eq_true (by omega'))
    have C2 := completion_monotonic job_cost sched j last t_busy LE C1
    rw [C2] at PEND; exact Bool.noConfusion PEND.2
  refine ⟨last, ⟨by omega', SPEC, ?_, ?_⟩, ?_⟩
  · intro t H Q
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    exact GREAT t H.1 (by omega') Q
  · simp only [Bool.and_eq_true]
    exact ⟨decide_eq_true JA, decide_eq_true (by omega')⟩
  · simp only [Bool.and_eq_true]
    exact ⟨decide_eq_true JA, decide_eq_true ARRj⟩

theorem busy_interval_has_uninterrupted_service {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (t_busy t1 : time) (H_is_busy_prefix : busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 (t_busy + 1))
    (priority_inversion_bound : time) (H_priority_inversion_is_bounded : priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j priority_inversion_bound) (delta : time) (H_delta_positive : 0 < delta) (H_no_quiet_time : ∀ t, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) :
    delta ≤ priority_inversion_bound + service_of_higher_or_equal_priority_jobs sched (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j t1 (t1 + delta) := by
  obtain ⟨H_strictly_larger, H_quiet, _, EXj⟩ := H_is_busy_prefix
  by_cases KLE : delta ≤ priority_inversion_bound
  · omega'
  have NOIDLE := no_idle_time_within_non_quiet_time_interval job_arrival job_cost arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j
    H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_work_conserving t1 delta H_no_quiet_time
  have HEP := hep_jobs_receive_no_service_before_quiet_time job_arrival job_cost arr_seq
    H_arrival_times_are_consistent sched higher_eq_priority j H_completed_jobs_dont_execute t1 H_quiet delta
  -- the service of lower-priority jobs is bounded by the cumulative priority inversion
  have LP : sumFiltered (jobs_arrived_between arr_seq 0 (t1 + delta)) (fun j' => !higher_eq_priority j' j)
      (fun j' => service_during sched j' t1 (t1 + delta)) ≤
      cumulative_priority_inversion sched higher_eq_priority j t1 (t1 + delta) := by
    unfold service_during cumulative_priority_inversion
    rw [sumFiltered_exchange]
    apply Finset.sum_le_sum
    intro t ht
    unfold is_priority_inversion
    cases SCHED : sched t with
    | none =>
      simp only [Bool.toNat_false, Nat.le_zero]
      apply sumFiltered_zero
      intro i _ _
      simp [service_at, scheduled_at, SCHED]
    | some j1 =>
      dsimp only
      cases PRIO1 : higher_eq_priority j1 j
      · simp only [Bool.not_false, Bool.toNat_true]
        exact service_of_jobs_le_1 job_arrival arr_seq H_arrival_times_are_consistent
          H_arrival_sequence_is_a_set sched 0 (t1 + delta) t (fun j' => !higher_eq_priority j' j)
      · simp only [Bool.not_true, Bool.toNat_false, Nat.le_zero]
        apply sumFiltered_zero
        intro i _ hi
        have NE : j1 ≠ i := by
          intro E; subst E; rw [PRIO1] at hi; exact Bool.noConfusion hi
        simp [service_at, scheduled_at, SCHED, NE]
  have SPLIT := sumFiltered_split (jobs_arrived_between arr_seq 0 (t1 + delta))
    (fun j' => higher_eq_priority j' j) (fun j' => service_during sched j' t1 (t1 + delta))
  unfold service_of_jobs at NOIDLE
  unfold service_of_higher_or_equal_priority_jobs service_of_jobs at HEP ⊢
  rw [HEP]
  -- the cumulative priority inversion is bounded by `priority_inversion_bound`
  have PIB : cumulative_priority_inversion sched higher_eq_priority j t1 (t1 + delta) ≤ priority_inversion_bound := by
    simp only [Bool.and_eq_true] at EXj
    have E1 := of_decide_eq_true EXj.1
    have E2 := of_decide_eq_true EXj.2
    by_cases NEQ : t1 + delta ≤ t_busy + 1
    · have M : cumulative_priority_inversion sched higher_eq_priority j t1 (t1 + delta) ≤
          cumulative_priority_inversion sched higher_eq_priority j t1 (t_busy + 1) := by
        unfold cumulative_priority_inversion
        exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico (Nat.le_refl _) NEQ)
      exact Nat.le_trans M (H_priority_inversion_is_bounded t1 (t_busy + 1)
        ⟨H_strictly_larger, H_quiet, by assumption, by simp only [Bool.and_eq_true]; exact ⟨EXj.1, EXj.2⟩⟩)
    · apply H_priority_inversion_is_bounded t1 (t1 + delta)
      refine ⟨by omega', H_quiet, ?_, ?_⟩
      · intro t' H
        simp only [Bool.and_eq_true, decide_eq_true_eq] at H
        exact H_no_quiet_time t' (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
      · simp only [Bool.and_eq_true]; exact ⟨decide_eq_true E1, decide_eq_true (by omega')⟩
  omega'

theorem busy_interval_too_much_workload {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job) (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (t_busy t1 : time) (H_is_busy_prefix : busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 (t_busy + 1)) (delta : time) (H_delta_positive : 0 < delta)
    (H_no_quiet_time : ∀ t, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) :
    service_of_higher_or_equal_priority_jobs sched (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j t1 (t1 + delta) < workload_of_higher_or_equal_priority_jobs job_cost (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j := by
  obtain ⟨_, QUIET, _⟩ := H_is_busy_prefix
  obtain ⟨j0, ARR0, BETWEEN0, HP0, NOTCOMP0⟩ := not_quiet_implies_exists_pending_job job_arrival job_cost arr_seq
    H_arrival_times_are_consistent sched higher_eq_priority j t1 (t1 + delta) (Nat.le_add_right _ _) QUIET
    (H_no_quiet_time (t1 + delta) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega'))
  have IN0 := arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j0 t1
    (t1 + delta) ARR0 BETWEEN0
  unfold service_of_higher_or_equal_priority_jobs service_of_jobs workload_of_higher_or_equal_priority_jobs
    workload_of_jobs
  apply ltn_sum_leq_seq _ _ _ _ j0 IN0 HP0
  · have B := BETWEEN0
    simp only [arrived_between, Bool.and_eq_true] at B
    have GE := of_decide_eq_true B.1
    have Z := cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j0 0 t1 GE
    have NC : ¬ (job_cost j0 ≤ service sched j0 (t1 + delta)) := fun h => NOTCOMP0 (decide_eq_true h)
    unfold service service_during at NC
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le t1) (Nat.le_add_right t1 delta), Z, Nat.zero_add] at NC
    unfold service_during
    omega'
  · intro i _ _
    exact cumulative_service_le_job_cost job_cost sched i H_completed_jobs_dont_execute t1 (t1 + delta)

theorem busy_interval_workload_larger_than_interval {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (t_busy t1 : time) (H_is_busy_prefix : busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 (t_busy + 1))
    (priority_inversion_bound : time) (H_priority_inversion_is_bounded : priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j priority_inversion_bound) (delta : time) (H_delta_positive : 0 < delta) (H_no_quiet_time : ∀ t, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true → ¬ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t) :
    delta < priority_inversion_bound + workload_of_higher_or_equal_priority_jobs job_cost (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j := by
  have A := busy_interval_has_uninterrupted_service job_arrival job_cost arr_seq H_arrival_times_are_consistent sched
    H_jobs_come_from_arrival_sequence higher_eq_priority j H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving t_busy t1 H_is_busy_prefix priority_inversion_bound
    H_priority_inversion_is_bounded delta H_delta_positive H_no_quiet_time
  have B := busy_interval_too_much_workload job_arrival job_cost arr_seq H_arrival_times_are_consistent sched
    higher_eq_priority j H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    t_busy t1 H_is_busy_prefix delta H_delta_positive H_no_quiet_time
  omega'

theorem busy_interval_is_bounded {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (t_busy t1 : time) (H_is_busy_prefix : busy_interval_prefix job_arrival job_cost arr_seq sched higher_eq_priority j t1 (t_busy + 1))
    (priority_inversion_bound : time) (H_priority_inversion_is_bounded : priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j priority_inversion_bound) (delta : time) (H_delta_positive : 0 < delta)
    (H_workload_is_bounded : priority_inversion_bound + workload_of_higher_or_equal_priority_jobs job_cost (jobs_arrived_between arr_seq t1 (t1 + delta)) higher_eq_priority j ≤ delta) :
    ∃ t2, t2 ≤ t1 + delta ∧ busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 := by
  classical
  by_cases EX : ∃ t, t1 < t ∧ t ≤ t1 + delta ∧ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t
  · have SPEC := Nat.find_spec EX
    have MIN : ∀ m, m < Nat.find EX → ¬ (t1 < m ∧ m ≤ t1 + delta ∧ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j m) :=
      fun m h => Nat.find_min EX h
    generalize Nat.find EX = t2 at SPEC MIN
    obtain ⟨GT, LE, QUIET2⟩ := SPEC
    obtain ⟨LT, QT1, NQ, IN⟩ := H_is_busy_prefix
    simp only [Bool.and_eq_true] at IN
    have IN1 := of_decide_eq_true IN.1
    have IN2 := of_decide_eq_true IN.2
    have NEQ : t_busy < t2 := by
      by_contra hc
      exact NQ t2 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega') QUIET2
    refine ⟨t2, LE, ⟨GT, QT1, ?_, ?_⟩, QUIET2⟩
    · intro t H Q
      simp only [Bool.and_eq_true, decide_eq_true_eq] at H
      exact MIN t H.2 ⟨H.1, by omega', Q⟩
    · simp only [Bool.and_eq_true]
      exact ⟨decide_eq_true IN1, decide_eq_true (by omega')⟩
  · push_neg at EX
    exfalso
    have TOOMUCH := busy_interval_workload_larger_than_interval job_arrival job_cost arr_seq
      H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j
      H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
      t_busy t1 H_is_busy_prefix priority_inversion_bound H_priority_inversion_is_bounded delta H_delta_positive
      (fun t H => by simp only [Bool.and_eq_true, decide_eq_true_eq] at H; exact EX t H.1 H.2)
    omega'

/-- LEAN_HELPER: a job with positive cost is pending at its arrival. -/
private theorem pending_at_arrival {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (j : Job)
    (H_positive_cost : 0 < job_cost j) :
    pending job_arrival job_cost sched j (job_arrival j) = true := by
  have Z := cumulative_service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j 0
    (job_arrival j) (Nat.le_refl _)
  have NC : ¬ (job_cost j ≤ service sched j (job_arrival j)) := by
    unfold service service_during; rw [Z]; omega'
  simp only [pending, has_arrived, completed_by, Bool.and_eq_true, Bool.not_eq_true']
  exact ⟨decide_eq_true (Nat.le_refl _), decide_eq_false NC⟩

theorem exists_busy_interval {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j) (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (priority_inversion_bound : time) (H_priority_inversion_is_bounded : priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j priority_inversion_bound)
    (delta : time) (H_delta_positive : 0 < delta)
    (H_workload_is_bounded : ∀ t, priority_inversion_bound + workload_of_higher_or_equal_priority_jobs job_cost (jobs_arrived_between arr_seq t (t + delta)) higher_eq_priority j ≤ delta)
    (H_positive_cost : 0 < job_cost j) :
    ∃ t1 t2, (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true ∧ t2 ≤ t1 + delta ∧ busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 := by
  obtain ⟨t1, PREFIX, H1⟩ := exists_busy_interval_prefix job_arrival job_cost arr_seq H_arrival_times_are_consistent
    sched higher_eq_priority j H_from_arrival_sequence H_priority_is_reflexive (job_arrival j)
    (pending_at_arrival job_arrival job_cost arr_seq sched H_jobs_must_arrive_to_execute j H_positive_cost)
  simp only [Bool.and_eq_true] at H1
  have GE1 := of_decide_eq_true H1.1
  obtain ⟨t2, GE2, BUSY⟩ := busy_interval_is_bounded job_arrival job_cost arr_seq H_arrival_times_are_consistent sched
    H_jobs_come_from_arrival_sequence higher_eq_priority j H_arrival_sequence_is_a_set H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving (job_arrival j) t1 PREFIX priority_inversion_bound
    H_priority_inversion_is_bounded delta H_delta_positive (H_workload_is_bounded t1)
  refine ⟨t1, t2, ?_, GE2, BUSY⟩
  simp only [Bool.and_eq_true]
  refine ⟨decide_eq_true GE1, decide_eq_true ?_⟩
  by_contra BUG
  obtain ⟨⟨LT12, _⟩, QUIET⟩ := BUSY
  exact PREFIX.2.2.1 t2 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega') QUIET

theorem busy_interval_bounds_response_time {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_from_arrival_sequence : arrives_in arr_seq j) (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (priority_inversion_bound : time) (H_priority_inversion_is_bounded : priority_inversion_of_job_is_bounded_by job_arrival job_cost arr_seq sched higher_eq_priority j priority_inversion_bound)
    (delta : time) (H_delta_positive : 0 < delta)
    (H_workload_is_bounded : ∀ t, priority_inversion_bound + workload_of_higher_or_equal_priority_jobs job_cost (jobs_arrived_between arr_seq t (t + delta)) higher_eq_priority j ≤ delta) :
    completed_by job_cost sched j (job_arrival j + delta) = true := by
  rcases Nat.eq_zero_or_pos (job_cost j) with Z | POS
  · simp [completed_by, Z]
  obtain ⟨t1, t2, H12, GE2, BUSY⟩ := exists_busy_interval job_arrival job_cost arr_seq H_arrival_times_are_consistent
    sched H_jobs_come_from_arrival_sequence higher_eq_priority j H_from_arrival_sequence H_arrival_sequence_is_a_set
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_priority_is_reflexive
    priority_inversion_bound H_priority_inversion_is_bounded delta H_delta_positive H_workload_is_bounded POS
  have COMP := job_completes_within_busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j
    H_from_arrival_sequence (fun x => H_priority_is_reflexive x) t1 t2 BUSY
  simp only [Bool.and_eq_true] at H12
  have A := of_decide_eq_true H12.1
  exact completion_monotonic job_cost sched j t2 _ (by omega') COMP

/-! ### Non-overloaded processor -/

def no_carry_in {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (t : time) : Prop :=
  ∀ j_o, arrives_in arr_seq j_o → arrived_before job_arrival j_o t = true → completed_by job_cost sched j_o t = true

theorem no_carry_in_implies_quiet_time {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) :
    ∀ (j : Job) (t : time), no_carry_in job_arrival job_cost arr_seq sched t → quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t := by
  intro j t FQT j_hp ARR _ BEF
  exact FQT j_hp ARR BEF

theorem idle_instant_implies_no_carry_in_at_t {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) :
    ∀ t : time, is_idle sched t = true → no_carry_in job_arrival job_cost arr_seq sched t := by
  intro t IDLE j ARR HA
  have IDLE' := of_decide_eq_true IDLE
  have HA' := of_decide_eq_true HA
  cases hc : completed_by job_cost sched j t
  · exfalso
    have BACK : backlogged job_arrival job_cost sched j t = true := by
      have hA : has_arrived job_arrival j t = true := decide_eq_true (by omega')
      have hS : scheduled_at sched j t = false := by simp [scheduled_at, IDLE']
      simp [backlogged, pending, hA, hc, hS]
    obtain ⟨jo, SCH⟩ := H_work_conserving j t ARR BACK
    simp [scheduled_at, IDLE'] at SCH
  · rfl

theorem idle_instant_implies_no_carry_in_at_t_pl_1 {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) :
    ∀ t : time, is_idle sched t = true → no_carry_in job_arrival job_cost arr_seq sched (t + 1) := by
  intro t IDLE j ARR HA
  have IDLE' := of_decide_eq_true IDLE
  have HA' := of_decide_eq_true HA
  cases hc : completed_by job_cost sched j (t + 1)
  · exfalso
    have NC : completed_by job_cost sched j t = false := by
      cases hct : completed_by job_cost sched j t
      · rfl
      · have := completion_monotonic job_cost sched j t (t + 1) (Nat.le_succ _) hct
        rw [hc] at this; exact Bool.noConfusion this
    have BACK : backlogged job_arrival job_cost sched j t = true := by
      have hA : has_arrived job_arrival j t = true := decide_eq_true (by omega')
      have hS : scheduled_at sched j t = false := by simp [scheduled_at, IDLE']
      simp [backlogged, pending, hA, NC, hS]
    obtain ⟨jo, SCH⟩ := H_work_conserving j t ARR BACK
    simp [scheduled_at, IDLE'] at SCH
  · rfl

theorem no_carry_in_at_the_beginning {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job) : no_carry_in job_arrival job_cost arr_seq sched 0 := by
  intro s _ AB
  simp [arrived_before] at AB

theorem total_service_is_bounded_by_Δ {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (sched : schedule Job) (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (Δ : time) (t : time) :
    service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) ≤ Δ := by
  have := service_of_jobs_le_delta sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true)
    (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0 (t + Δ)) t (t + Δ)
  omega'

theorem low_total_service_implies_existence_of_time_with_no_carry_in {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (Δ : time) (H_delta_positive : 0 < Δ) (t : time) :
    service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) < Δ → ∃ δ, δ < Δ ∧ no_carry_in job_arrival job_cost arr_seq sched (t + 1 + δ) := by
  intro LT
  obtain ⟨t_idle, RANGE, IDLE⟩ := low_service_implies_existence_of_idle_time job_arrival arr_seq
    H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_jobs_come_from_arrival_sequence t (t + Δ)
    (Nat.le_add_right _ _) (by omega')
  simp only [Bool.and_eq_true, decide_eq_true_eq] at RANGE
  rcases Nat.eq_or_lt_of_le RANGE.1 with EQ | GT
  · subst EQ
    exact ⟨0, H_delta_positive, by
      rw [Nat.add_zero]
      exact idle_instant_implies_no_carry_in_at_t_pl_1 job_arrival job_cost arr_seq sched H_work_conserving t IDLE⟩
  · refine ⟨t_idle - t - 1, by omega', ?_⟩
    rw [show t + 1 + (t_idle - t - 1) = t_idle by omega']
    exact idle_instant_implies_no_carry_in_at_t job_arrival job_cost arr_seq sched H_work_conserving t_idle IDLE

theorem completion_of_all_jobs_implies_no_carry_in {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (Δ : time) (H_workload_is_bounded : ∀ t, workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + Δ)) (fun _ => true) ≤ Δ) (t : time) (H_no_carry_in : no_carry_in job_arrival job_cost arr_seq sched t) :
    service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) t (t + Δ) = Δ → no_carry_in job_arrival job_cost arr_seq sched (t + Δ) := by
  intro EQserv
  have COMPL := all_jobs_have_completed_impl_workload_eq_service job_arrival job_cost arr_seq
    H_arrival_times_are_consistent sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute (fun _ => true)
    0 t t (fun j IN _ => H_no_carry_in j (in_arrivals_implies_arrived arr_seq j 0 t IN)
      (in_arrivals_implies_arrived_before job_arrival arr_seq H_arrival_times_are_consistent j t IN))
  have WCAT := workload_of_jobs_cat job_cost arr_seq t 0 (t + Δ) (fun _ => true)
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Nat.zero_le _, Nat.le_add_right _ _⟩)
  have SCAT := service_of_jobs_cat_scheduling_interval job_arrival arr_seq H_arrival_times_are_consistent sched
    H_jobs_must_arrive_to_execute (fun _ => true) 0 (t + Δ) t
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Nat.zero_le _, Nat.le_add_right _ _⟩)
  have ACAT := service_of_jobs_cat_arrival_interval arr_seq sched (fun _ => true) 0 (t + Δ) t
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Nat.zero_le _, Nat.le_add_right _ _⟩)
  have LEW := service_of_jobs_le_workload job_cost sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true)
    H_completed_jobs_dont_execute 0 (t + Δ)
  have WB := H_workload_is_bounded t
  have EQ : workload_of_jobs job_cost (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) =
      service_of_jobs sched (jobs_arrived_between arr_seq 0 (t + Δ)) (fun _ => true) 0 (t + Δ) := by
    omega'
  intro s ARR BEF
  exact workload_eq_service_impl_all_jobs_have_completed job_arrival job_cost arr_seq H_arrival_times_are_consistent
    sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute (fun _ => true) 0 (t + Δ) (t + Δ) EQ s
    (arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent s 0 (t + Δ) ARR
      (by simp only [arrived_between, Bool.and_eq_true]; exact ⟨decide_eq_true (Nat.zero_le _), BEF⟩)) rfl

theorem processor_is_not_too_busy {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq) (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (Δ : time) (H_delta_positive : 0 < Δ) (H_workload_is_bounded : ∀ t, workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + Δ)) (fun _ => true) ≤ Δ) :
    ∀ t : time, ∃ δ, δ < Δ ∧ no_carry_in job_arrival job_cost arr_seq sched (t + δ) := by
  intro t
  induction t with
  | zero => exact ⟨0, H_delta_positive, by simpa using no_carry_in_at_the_beginning job_arrival job_cost arr_seq sched⟩
  | succ t IH =>
    obtain ⟨δ, LE, FQT⟩ := IH
    rcases Nat.eq_zero_or_pos δ with Z | POS
    · subst Z
      rw [Nat.add_zero] at FQT
      rcases Nat.eq_or_lt_of_le (total_service_is_bounded_by_Δ job_arrival arr_seq H_arrival_times_are_consistent
          sched H_arrival_sequence_is_a_set Δ t) with EQ | LT
      · refine ⟨Δ - 1, by omega', ?_⟩
        rw [show t + 1 + (Δ - 1) = t + Δ by omega']
        exact completion_of_all_jobs_implies_no_carry_in job_arrival job_cost arr_seq H_arrival_times_are_consistent
          sched H_completed_jobs_dont_execute H_jobs_must_arrive_to_execute Δ H_workload_is_bounded t FQT EQ
      · exact low_total_service_implies_existence_of_time_with_no_carry_in job_arrival job_cost arr_seq
          H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence H_work_conserving
          H_jobs_must_arrive_to_execute Δ H_delta_positive t LT
    · refine ⟨δ - 1, by omega', ?_⟩
      rw [show t + 1 + (δ - 1) = t + δ by omega']
      exact FQT

theorem exists_busy_interval_from_total_workload_bound {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (higher_eq_priority : JLFP_policy Job) (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (Δ : time) (H_delta_positive : 0 < Δ)
    (H_workload_is_bounded : ∀ t, workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + Δ)) (fun _ => true) ≤ Δ) (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j)
    (H_job_cost_positive : job_cost_positive job_cost j = true) :
    ∃ t1 t2, (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true ∧ t2 ≤ t1 + Δ ∧ busy_interval job_arrival job_cost arr_seq sched higher_eq_priority j t1 t2 := by
  classical
  obtain ⟨t1, PREFIX, H1⟩ := exists_busy_interval_prefix job_arrival job_cost arr_seq H_arrival_times_are_consistent
    sched higher_eq_priority j H_from_arrival_sequence H_priority_is_reflexive (job_arrival j)
    (pending_at_arrival job_arrival job_cost arr_seq sched H_jobs_must_arrive_to_execute j
      (of_decide_eq_true H_job_cost_positive))
  simp only [Bool.and_eq_true] at H1
  have GE1 := of_decide_eq_true H1.1
  obtain ⟨δ, LE, QT⟩ := processor_is_not_too_busy job_arrival job_cost arr_seq H_arrival_times_are_consistent sched
    H_jobs_come_from_arrival_sequence H_arrival_sequence_is_a_set H_work_conserving H_completed_jobs_dont_execute
    H_jobs_must_arrive_to_execute Δ H_delta_positive H_workload_is_bounded (t1 + 1)
  have QT' := no_carry_in_implies_quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j _ QT
  have EX : ∃ t2, t1 < t2 ∧ t2 ≤ t1 + 1 + δ ∧ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j t2 := ⟨t1 + 1 + δ, by omega', Nat.le_refl _, QT'⟩
  have SPEC := Nat.find_spec EX
  have MIN : ∀ m, m < Nat.find EX → ¬ (t1 < m ∧ m ≤ t1 + 1 + δ ∧ quiet_time job_arrival job_cost arr_seq sched higher_eq_priority j m) := fun m h => Nat.find_min EX h
  generalize Nat.find EX = t2 at SPEC MIN
  obtain ⟨GT, LEt2, QUIET⟩ := SPEC
  obtain ⟨LT, QTt1, NQT, _⟩ := PREFIX
  have NEQ : job_arrival j < t2 := by
    by_contra hc
    exact NQT t2 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega') QUIET
  refine ⟨t1, t2, ?_, by omega', ⟨GT, QTt1, ?_, ?_⟩, QUIET⟩
  · simp only [Bool.and_eq_true]; exact ⟨decide_eq_true GE1, decide_eq_true NEQ⟩
  · intro t H Q
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    exact MIN t H.2 ⟨H.1, by omega', Q⟩
  · simp only [Bool.and_eq_true]; exact ⟨decide_eq_true GE1, decide_eq_true NEQ⟩

end Prosa.Classic.Model.Schedule.Uni.Limited.BusyInterval.BusyIntervalJLFP
