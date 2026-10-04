-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/jitter/busy_interval.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 81)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform

/-!
Busy intervals in jitter-aware uniprocessor schedules (Rocq module `BusyInterval`).

Representation notes:
* `pending`/`backlogged` are the jitter-aware `UniprocessorScheduleWithJitter` definitions; `work_conserving` and
  `respects_JLFP_policy` are the jitter-aware `Platform` definitions.
* Boolean tests in proposition position are `= true`; `~ P` is `¬ P`; Boolean chains `a < x < b`, `a <= x < b`,
  `a < x <= b` in proposition position are `(decide (…) && decide (…)) = true`; `t.+1` is `t + 1`.
* The section-local `Let`s (`job_pending_at`, `job_scheduled_at`, `job_completed_by`, `actual_job_arrival`,
  `actual_job_arrival_between`, `actual_arrivals`, `actual_hp_workload`, `actual_hp_service`) are unfolded.
* Binder lists follow the Rocq contract (e.g. `not_quiet_implies_not_idle` takes neither `H_quiet` nor
  `H_completed_jobs_dont_execute`; `busy_interval_is_bounded` takes `t_busy` and `H_is_busy_prefix` but neither
  `H_j_is_pending` nor `H_busy_prefix_contains_arrival`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Jitter.BusyInterval.BusyInterval

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule hiding pending backlogged scheduled_implies_pending
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Uni.Service.Service
open Prosa.Classic.Model.Schedule.Uni.Workload.Workload
open Prosa.Util.Sum (sumFiltered ltn_sum_leq_seq)

universe v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def quiet_time {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (t : time) : Prop :=
  ∀ j_hp, arrives_in arr_seq j_hp → higher_eq_priority j_hp j = true →
    actual_arrival_before job_arrival job_jitter j_hp t = true → completed_by job_cost sched j_hp t = true

def busy_interval_prefix {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (t1 t_busy : time) : Prop :=
  t1 < t_busy ∧
  quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 ∧
  (∀ t, (decide (t1 < t) && decide (t < t_busy)) = true →
    ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t)

def busy_interval {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (sched : schedule Job) (higher_eq_priority : JLFP_policy Job) (j : Job)
    (t1 t2 : time) : Prop :=
  busy_interval_prefix job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 t2 ∧
  quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t2

/-! ### Proof-local helpers -/

private theorem sumFiltered_exchange' {I : Type _} (l : List I) (P : I → Bool) (f : I → Nat → Nat) (t1 t2 : Nat) :
    sumFiltered l P (fun i => ∑ t ∈ Finset.Ico t1 t2, f i t) =
      ∑ t ∈ Finset.Ico t1 t2, sumFiltered l P (fun i => f i t) := by
  unfold sumFiltered
  induction (l.filter P) with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]

private theorem sum_service_at_le_one' {Job : Type v} [DecidableEq Job] (sched : schedule Job) (t : Nat)
    (l : List Job) (hl : l.Nodup) : (l.map (fun j => service_at sched j t)).sum ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons]
    by_cases hs : sched t = some a
    · have : (l.map (fun j => service_at sched j t)).sum = 0 := by
        apply List.sum_eq_zero
        intro x hx
        obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
        have hne : j ≠ a := fun h => hl.1 (h ▸ hj)
        simp [service_at, scheduled_at, hs, Ne.symm hne]
      rw [this]; simp [service_at, scheduled_at, hs]
    · have h0 : service_at sched a t = 0 := by simp [service_at, scheduled_at, hs]
      rw [h0, Nat.zero_add]; exact ih hl.2

/-- LEAN_HELPER: a job is pending at its actual arrival if it has positive cost. -/
private theorem pending_at_actual_arrival {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_jitter : Job → time)
    (sched : schedule Job) (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (j : Job) (H_positive_cost : 0 < job_cost j) :
    pending job_arrival job_cost job_jitter sched j (actual_arrival job_arrival job_jitter j) = true := by
  have Z := cumulative_service_before_jitter_is_zero job_arrival job_jitter sched H_jobs_execute_after_jitter j 0
    (actual_arrival job_arrival job_jitter j) (Nat.le_refl _)
  simp only [pending, jitter_has_passed, completed_by, service, service_during, Z, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]
  exact ⟨by simp, by omega'⟩

/-! ### Lemmas -/

theorem job_completes_within_busy_interval {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 t2)
    (t : time) (H_during_interval : (decide (t1 ≤ t) && decide (t < t2)) = true)
    (H_job_is_pending : pending job_arrival job_cost job_jitter sched j t = true) :
    completed_by job_cost sched j t2 = true := by
  obtain ⟨_, QUIET⟩ := H_busy_interval
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H_during_interval
  simp only [pending, Bool.and_eq_true] at H_job_is_pending
  have ARR := of_decide_eq_true H_job_is_pending.1
  apply QUIET j H_from_arrival_sequence (H_priority_is_reflexive j)
  simp only [actual_arrival_before, decide_eq_true_eq]
  omega'

theorem job_arrives_within_busy_interval {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (t1 t2 : time)
    (H_busy_interval : busy_interval job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 t2)
    (t : time) (H_during_interval : (decide (t1 ≤ t) && decide (t < t2)) = true)
    (H_job_is_pending : pending job_arrival job_cost job_jitter sched j t = true) :
    t1 ≤ actual_arrival job_arrival job_jitter j := by
  by_contra LT1
  obtain ⟨⟨_, QUIET, _⟩, _⟩ := H_busy_interval
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H_during_interval
  simp only [pending, Bool.and_eq_true, Bool.not_eq_true'] at H_job_is_pending
  have C1 := QUIET j H_from_arrival_sequence (H_priority_is_reflexive j)
    (by simp only [actual_arrival_before, decide_eq_true_eq]; omega')
  have C2 := completion_monotonic job_cost sched j t1 t H_during_interval.1 C1
  rw [C2] at H_job_is_pending
  exact Bool.noConfusion H_job_is_pending.2

theorem not_quiet_implies_exists_pending_job {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (t1 t2 : time) (H_interval : t1 ≤ t2)
    (H_quiet : quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1)
    (H_not_quiet : ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t2) :
    ∃ j_hp, arrives_in arr_seq j_hp ∧ actual_arrival_between job_arrival job_jitter j_hp t1 t2 = true ∧
      higher_eq_priority j_hp j = true ∧ ¬ (completed_by job_cost sched j_hp t2 = true) := by
  by_contra NONE
  push_neg at NONE
  apply H_not_quiet
  intro j_hp IN HP ARR
  have ARR' := of_decide_eq_true ARR
  by_cases h : actual_arrival job_arrival job_jitter j_hp < t1
  · exact completion_monotonic job_cost sched j_hp t1 t2 H_interval
      (H_quiet j_hp IN HP (by simp only [actual_arrival_before, decide_eq_true_eq]; exact h))
  · exact NONE j_hp IN (by simp only [actual_arrival_between, Bool.and_eq_true, decide_eq_true_eq]; omega') HP

theorem not_quiet_implies_not_idle {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched) (t1 t2 : time)
    (H_strictly_larger : t1 < t2)
    (H_not_quiet : ∀ t, (decide (t1 < t) && decide (t ≤ t2)) = true →
      ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t) :
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t ≤ t2)) = true → ¬ (is_idle sched t = true) := by
  intro t H IDLE
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  simp only [is_idle, decide_eq_true_eq] at IDLE
  -- any pending job at an idle instant contradicts work conservation
  have NOBACK : ∀ j_hp, arrives_in arr_seq j_hp →
      backlogged job_arrival job_cost job_jitter sched j_hp t = true → False := by
    intro j_hp IN BACK
    obtain ⟨j_other, SCHEDother⟩ := H_work_conserving j_hp t IN BACK
    simp [scheduled_at, IDLE] at SCHEDother
  have NOTSCHED : ∀ j_hp, scheduled_at sched j_hp t = false := by
    intro j_hp; simp [scheduled_at, IDLE]
  rcases Nat.eq_or_lt_of_le H.1 with EQUAL | LARGER
  · subst EQUAL
    apply H_not_quiet (t1 + 1) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    intro j_hp IN HP ARR
    apply completion_monotonic job_cost sched j_hp t1 (t1 + 1) (Nat.le_succ _)
    cases hc : completed_by job_cost sched j_hp t1
    · exfalso
      apply NOBACK j_hp IN
      have ARR' := of_decide_eq_true ARR
      simp only [backlogged, pending, jitter_has_passed, hc, NOTSCHED, Bool.not_false, Bool.and_true,
        decide_eq_true_eq]
      omega'
    · rfl
  · apply H_not_quiet t (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
    intro j_hp IN HP ARR
    cases hc : completed_by job_cost sched j_hp t
    · exfalso
      apply NOBACK j_hp IN
      have ARR' := of_decide_eq_true ARR
      simp only [backlogged, pending, jitter_has_passed, hc, NOTSCHED, Bool.not_false, Bool.and_true,
        decide_eq_true_eq]
      omega'
    · rfl

theorem not_quiet_implies_exists_scheduled_hp_job {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched) (t1 t2 : time)
    (H_strictly_larger : t1 < t2)
    (H_quiet : quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1)
    (H_not_quiet : ∀ t, (decide (t1 < t) && decide (t ≤ t2)) = true →
      ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority)
    (H_respects_policy : respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority) :
    ∀ t : Nat, (decide (t1 ≤ t) && decide (t < t2)) = true →
      ∃ j_hp, actual_arrival_between job_arrival job_jitter j_hp t1 t2 = true ∧
        higher_eq_priority j_hp j = true ∧ scheduled_at sched j_hp t = true := by
  intro t H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  have NOTIDLE := not_quiet_implies_not_idle job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j
    H_work_conserving t1 t2 H_strictly_larger H_not_quiet t
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
  cases SCHED : sched t with
  | none => exact absurd (by simp [is_idle, SCHED]) NOTIDLE
  | some j_hp =>
    have SCHEDhp : scheduled_at sched j_hp t = true := by simp [scheduled_at, SCHED]
    have HP : higher_eq_priority j_hp j = true := by
      by_contra NOTHP
      apply H_not_quiet (t + 1) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
      intro j_hp' IN HP' ARR
      by_contra NOTCOMP'
      have NOTCOMPt : completed_by job_cost sched j_hp' t = false := by
        cases hc : completed_by job_cost sched j_hp' t
        · rfl
        · exact absurd (completion_monotonic job_cost sched j_hp' t (t + 1) (Nat.le_succ t) hc) NOTCOMP'
      have NOTSCHED' : scheduled_at sched j_hp' t = false := by
        cases hs : scheduled_at sched j_hp' t
        · rfl
        · have EQ := only_one_job_scheduled sched j_hp j_hp' t SCHEDhp hs
          subst EQ; exact absurd HP' NOTHP
      have BACK : backlogged job_arrival job_cost job_jitter sched j_hp' t = true := by
        have ARR' := of_decide_eq_true ARR
        simp only [backlogged, pending, jitter_has_passed, NOTCOMPt, NOTSCHED', Bool.not_false, Bool.and_true,
          decide_eq_true_eq]
        omega'
      have := H_respects_policy j_hp' j_hp t IN BACK SCHEDhp
      exact NOTHP (H_priority_is_transitive j_hp' j_hp j this HP')
    refine ⟨j_hp, ?_, HP, SCHEDhp⟩
    have PASS := of_decide_eq_true (H_jobs_execute_after_jitter j_hp t SCHEDhp)
    simp only [actual_arrival_between, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, by omega'⟩
    by_contra LT
    have C1 := H_quiet j_hp (H_jobs_come_from_arrival_sequence j_hp t SCHEDhp) HP
      (by simp only [actual_arrival_before, decide_eq_true_eq]; omega')
    have C2 := completion_monotonic job_cost sched j_hp t1 t H.1 C1
    have := completed_implies_not_scheduled job_cost sched j_hp H_completed_jobs_dont_execute t C2
    rw [SCHEDhp] at this; exact Bool.noConfusion this

theorem exists_busy_interval_prefix {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority) (t_busy : time)
    (H_j_is_pending : pending job_arrival job_cost job_jitter sched j t_busy = true) :
    ∃ t1, busy_interval_prefix job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 (t_busy + 1) ∧
      (decide (t1 ≤ actual_arrival job_arrival job_jitter j) &&
        decide (actual_arrival job_arrival job_jitter j ≤ t_busy)) = true := by
  classical
  have Q0 : quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j 0 := by
    intro j_hp _ _ ARR; simp [actual_arrival_before] at ARR
  have SPEC := Nat.findGreatest_spec
    (P := fun t => quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t)
    (Nat.zero_le t_busy) Q0
  have LE := Nat.findGreatest_le
    (P := fun t => quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t) t_busy
  have GREAT : ∀ k, Nat.findGreatest
      (fun t => quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t) t_busy < k →
      k ≤ t_busy → ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j k :=
    fun k h hk => Nat.findGreatest_is_greatest h hk
  generalize Nat.findGreatest
    (fun t => quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t) t_busy = last
    at SPEC LE GREAT
  have PEND := H_j_is_pending
  simp only [pending, Bool.and_eq_true, Bool.not_eq_true'] at PEND
  have ARRj := of_decide_eq_true PEND.1
  refine ⟨last, ⟨by omega', SPEC, ?_⟩, ?_⟩
  · intro t H Q
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    exact GREAT t H.1 (by omega') Q
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨?_, ARRj⟩
    by_contra hc
    have C1 := SPEC j H_from_arrival_sequence (H_priority_is_reflexive j)
      (by simp only [actual_arrival_before, decide_eq_true_eq]; omega')
    have C2 := completion_monotonic job_cost sched j last t_busy LE C1
    rw [C2] at PEND; exact Bool.noConfusion PEND.2

theorem busy_interval_has_uninterrupted_service {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_policy : respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (t_busy t1 : time)
    (H_is_busy_prefix :
      busy_interval_prefix job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 (t_busy + 1))
    (delta : time) (H_delta_positive : 0 < delta)
    (H_no_quiet_time : ∀ t, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true →
      ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t) :
    service_of_higher_or_equal_priority_jobs sched (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
      higher_eq_priority j t1 (t1 + delta) = delta := by
  obtain ⟨_, QUIET, _⟩ := H_is_busy_prefix
  have UNIQ := actual_arrivals_uniq job_arrival job_jitter arr_seq H_arrival_times_are_consistent
    H_arrival_sequence_is_a_set t1 (t1 + delta)
  unfold service_of_higher_or_equal_priority_jobs service_of_jobs service_during
  rw [sumFiltered_exchange']
  calc _ = ∑ _t ∈ Finset.Ico t1 (t1 + delta), (1 : Nat) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Finset.mem_Ico] at ht
        obtain ⟨j_hp, BETWEEN, HP, SCHED⟩ := not_quiet_implies_exists_scheduled_hp_job job_arrival job_cost job_jitter
          arr_seq sched H_jobs_come_from_arrival_sequence higher_eq_priority j H_work_conserving
          H_completed_jobs_dont_execute H_jobs_execute_after_jitter t1 (t1 + delta) (by omega') QUIET
          H_no_quiet_time H_priority_is_transitive H_respects_policy t
          (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')
        have IN := arrived_between_implies_in_actual_arrivals job_arrival job_jitter arr_seq
          H_arrival_times_are_consistent j_hp t1 (t1 + delta) (H_jobs_come_from_arrival_sequence j_hp t SCHED) BETWEEN
        apply Nat.le_antisymm
        · exact sum_service_at_le_one' sched t _ (UNIQ.filter _)
        · have h1 : service_at sched j_hp t = 1 := by simp [service_at, SCHED]
          have := List.le_sum_of_mem (List.mem_map_of_mem (f := fun i => service_at sched i t)
            ((List.mem_filter (p := fun j_hp => higher_eq_priority j_hp j)).mpr ⟨IN, HP⟩))
          unfold sumFiltered; omega'
    _ = delta := by simp

theorem busy_interval_too_much_workload {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (t_busy t1 : time)
    (H_is_busy_prefix :
      busy_interval_prefix job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 (t_busy + 1))
    (delta : time) (H_delta_positive : 0 < delta)
    (H_no_quiet_time : ∀ t, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true →
      ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t) :
    service_of_higher_or_equal_priority_jobs sched (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta))
        higher_eq_priority j t1 (t1 + delta) <
      workload_of_higher_or_equal_priority_jobs job_cost
        (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta)) higher_eq_priority j := by
  obtain ⟨_, QUIET, _⟩ := H_is_busy_prefix
  obtain ⟨j0, ARR0, BETWEEN0, HP0, NOTCOMP0⟩ := not_quiet_implies_exists_pending_job job_arrival job_cost job_jitter
    arr_seq H_arrival_times_are_consistent sched higher_eq_priority j t1 (t1 + delta) (Nat.le_add_right _ _) QUIET
    (H_no_quiet_time (t1 + delta) (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega'))
  have IN0 := arrived_between_implies_in_actual_arrivals job_arrival job_jitter arr_seq
    H_arrival_times_are_consistent j0 t1 (t1 + delta) ARR0 BETWEEN0
  unfold service_of_higher_or_equal_priority_jobs service_of_jobs workload_of_higher_or_equal_priority_jobs
    workload_of_jobs
  apply ltn_sum_leq_seq _ _ _ _ j0 IN0 HP0
  · have B := BETWEEN0
    simp only [actual_arrival_between, Bool.and_eq_true] at B
    have GE := of_decide_eq_true B.1
    have Z := cumulative_service_before_jitter_is_zero job_arrival job_jitter sched H_jobs_execute_after_jitter j0 0 t1
      GE
    have NC : ¬ (job_cost j0 ≤ service sched j0 (t1 + delta)) := fun h => NOTCOMP0 (decide_eq_true h)
    unfold service service_during at NC
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le t1) (Nat.le_add_right t1 delta), Z, Nat.zero_add] at NC
    unfold service_during
    omega'
  · intro i _ _
    exact cumulative_service_le_job_cost job_cost sched i H_completed_jobs_dont_execute t1 (t1 + delta)

theorem busy_interval_workload_larger_than_interval {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_policy : respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (t_busy t1 : time)
    (H_is_busy_prefix :
      busy_interval_prefix job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 (t_busy + 1))
    (delta : time) (H_delta_positive : 0 < delta)
    (H_no_quiet_time : ∀ t, (decide (t1 < t) && decide (t ≤ t1 + delta)) = true →
      ¬ quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t) :
    delta < workload_of_higher_or_equal_priority_jobs job_cost
      (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta)) higher_eq_priority j := by
  have SERV := busy_interval_has_uninterrupted_service job_arrival job_cost job_jitter arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j
    H_arrival_sequence_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving
    H_respects_policy H_priority_is_transitive t_busy t1 H_is_busy_prefix delta H_delta_positive H_no_quiet_time
  have MORE := busy_interval_too_much_workload job_arrival job_cost job_jitter arr_seq H_arrival_times_are_consistent
    sched higher_eq_priority j H_arrival_sequence_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute
    t_busy t1 H_is_busy_prefix delta H_delta_positive H_no_quiet_time
  omega'

theorem busy_interval_is_bounded {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (higher_eq_priority : JLFP_policy Job) (j : Job)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_policy : respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (t_busy t1 : time)
    (H_is_busy_prefix :
      busy_interval_prefix job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 (t_busy + 1))
    (delta : time) (H_delta_positive : 0 < delta)
    (H_workload_is_bounded : workload_of_higher_or_equal_priority_jobs job_cost
      (actual_arrivals_between job_arrival job_jitter arr_seq t1 (t1 + delta)) higher_eq_priority j ≤ delta) :
    ∃ t2, t2 ≤ t1 + delta ∧
      busy_interval job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 t2 := by
  classical
  by_cases EX : ∃ t, t1 < t ∧ t ≤ t1 + delta ∧
      quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t
  · have SPEC := Nat.find_spec EX
    have MIN : ∀ m, m < Nat.find EX → ¬ (t1 < m ∧ m ≤ t1 + delta ∧
        quiet_time job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j m) :=
      fun m h => Nat.find_min EX h
    generalize Nat.find EX = t2 at SPEC MIN
    obtain ⟨GT, LE, QUIET2⟩ := SPEC
    refine ⟨t2, LE, ⟨GT, H_is_busy_prefix.2.1, ?_⟩, QUIET2⟩
    intro t H Q
    simp only [Bool.and_eq_true, decide_eq_true_eq] at H
    exact MIN t H.2 ⟨H.1, by omega', Q⟩
  · push_neg at EX
    exfalso
    have TOOMUCH := busy_interval_workload_larger_than_interval job_arrival job_cost job_jitter arr_seq
      H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j
      H_arrival_sequence_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving
      H_respects_policy H_priority_is_transitive t_busy t1 H_is_busy_prefix delta H_delta_positive
      (fun t H => by simp only [Bool.and_eq_true, decide_eq_true_eq] at H; exact EX t H.1 H.2)
    omega'

theorem exists_busy_interval {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_policy : respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (delta : time) (H_delta_positive : 0 < delta)
    (H_workload_is_bounded : ∀ t, workload_of_higher_or_equal_priority_jobs job_cost
      (actual_arrivals_between job_arrival job_jitter arr_seq t (t + delta)) higher_eq_priority j ≤ delta)
    (H_positive_cost : 0 < job_cost j) :
    ∃ t1 t2, (decide (t1 ≤ actual_arrival job_arrival job_jitter j) &&
        decide (actual_arrival job_arrival job_jitter j < t2)) = true ∧
      t2 ≤ t1 + delta ∧ busy_interval job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j t1 t2 := by
  have PEND := pending_at_actual_arrival job_arrival job_cost job_jitter sched H_jobs_execute_after_jitter j
    H_positive_cost
  obtain ⟨t1, PREFIX, H1⟩ := exists_busy_interval_prefix job_arrival job_cost job_jitter arr_seq
    H_arrival_times_are_consistent sched higher_eq_priority j H_from_arrival_sequence H_priority_is_reflexive
    (actual_arrival job_arrival job_jitter j) PEND
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H1
  obtain ⟨t2, GE2, BUSY⟩ := busy_interval_is_bounded job_arrival job_cost job_jitter arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j
    H_arrival_sequence_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving
    H_respects_policy H_priority_is_transitive (actual_arrival job_arrival job_jitter j) t1 PREFIX delta
    H_delta_positive (H_workload_is_bounded t1)
  refine ⟨t1, t2, ?_, GE2, BUSY⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨H1.1, ?_⟩
  by_contra BUG
  obtain ⟨⟨LT12, _⟩, QUIET⟩ := BUSY
  exact PREFIX.2.2 t2 (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') QUIET

theorem busy_interval_bounds_response_time {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (higher_eq_priority : JLFP_policy Job) (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_policy : respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched higher_eq_priority)
    (H_priority_is_reflexive : JLFP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : JLFP_is_transitive higher_eq_priority) (delta : time) (H_delta_positive : 0 < delta)
    (H_workload_is_bounded : ∀ t, workload_of_higher_or_equal_priority_jobs job_cost
      (actual_arrivals_between job_arrival job_jitter arr_seq t (t + delta)) higher_eq_priority j ≤ delta) :
    completed_by job_cost sched j (actual_arrival job_arrival job_jitter j + delta) = true := by
  rcases Nat.eq_zero_or_pos (job_cost j) with Z | POS
  · simp [completed_by, Z]
  obtain ⟨t1, t2, H12, GE2, BUSY⟩ := exists_busy_interval job_arrival job_cost job_jitter arr_seq
    H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence higher_eq_priority j H_from_arrival_sequence
    H_arrival_sequence_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving
    H_respects_policy H_priority_is_reflexive H_priority_is_transitive delta H_delta_positive H_workload_is_bounded POS
  have COMP := job_completes_within_busy_interval job_arrival job_cost job_jitter arr_seq sched higher_eq_priority j
    H_from_arrival_sequence H_priority_is_reflexive t1 t2 BUSY (actual_arrival job_arrival job_jitter j) H12
    (pending_at_actual_arrival job_arrival job_cost job_jitter sched H_jobs_execute_after_jitter j POS)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H12
  exact completion_monotonic job_cost sched j t2 _ (by omega') COMP

end Prosa.Classic.Model.Schedule.Uni.Jitter.BusyInterval.BusyInterval
