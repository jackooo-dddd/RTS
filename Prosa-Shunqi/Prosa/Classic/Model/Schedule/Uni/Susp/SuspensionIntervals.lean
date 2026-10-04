-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/susp/suspension_intervals.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 73)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution

/-!
Suspension intervals in uniprocessor schedules (Rocq module `SuspensionIntervals`, which `Export`s `Job`,
`UniprocessorSchedule`, `Suspension` and `LastExecution`).

Representation notes:
* `suspended_at` is a Boolean: `~~ completed_by … && (start <= t < start + duration)` is
  `!completed_by … && (decide (start ≤ t) && decide (t < start + duration))`.
* `\sum_(t1 <= t < t2) (suspended_at j t)` (a Boolean summed as a number) is
  `∑ t ∈ Finset.Ico t1 t2, (suspended_at … j t).toNat`.
* The section-local `Let`s (`job_scheduled_at`, `job_completed_by`, `suspension_start`, `current_service`,
  `duration`, `cumulative_suspension_of_j`, `total_suspension_of_j`) are unfolded.
* Boolean tests in proposition position are `= true`; `~ P` is `¬ P`; `t.+1` is `t + 1`.
* Binder lists follow the Rocq contract (e.g. `same_service_in_suspension_interval` does not take
  `H_has_arrived`, and `suspended_implies_not_completed` takes only `H_j_is_suspended`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Susp.LastExecution.LastExecution

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def suspension_duration {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (j : Job) (t : time) : duration :=
  next_suspension j (service sched j (time_after_last_execution job_arrival sched j t))

def suspended_at {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (j : Job) (t : time) : Bool :=
  !completed_by job_cost sched j t &&
    (decide (time_after_last_execution job_arrival sched j t ≤ t) &&
      decide (t < time_after_last_execution job_arrival sched j t +
        suspension_duration job_arrival next_suspension sched j t))

def cumulative_suspension_during {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (j : Job) (t1 t2 : time) : Nat :=
  ∑ t ∈ Finset.Ico t1 t2, (suspended_at job_arrival job_cost next_suspension sched j t).toNat

def cumulative_suspension {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (j : Job) (t : time) : Nat :=
  cumulative_suspension_during job_arrival job_cost next_suspension sched j 0 t

def respects_self_suspensions {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) : Prop :=
  ∀ j t, scheduled_at sched j t = true → ¬ (suspended_at job_arrival job_cost next_suspension sched j t = true)

theorem same_service_in_suspension_interval {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (j : Job) (t t_in : time)
    (H_within_suspension_interval :
      (decide (time_after_last_execution job_arrival sched j t ≤ t_in) &&
        decide (t_in ≤ time_after_last_execution job_arrival sched j t +
          suspension_duration job_arrival next_suspension sched j t)) = true) :
    service sched j t_in = service sched j (time_after_last_execution job_arrival sched j t) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H_within_suspension_interval
  obtain ⟨GE, LE⟩ := H_within_suspension_interval
  unfold suspension_duration at LE
  have IDEM := last_execution_idempotent job_arrival sched H_jobs_must_arrive_to_execute j t
  generalize time_after_last_execution job_arrival sched j t = b at GE LE IDEM ⊢
  suffices SAME : ∀ delta, delta ≤ next_suspension j (service sched j b) →
      service sched j (b + delta) = service sched j b by
    have := SAME (t_in - b) (by omega')
    rwa [show b + (t_in - b) = t_in by omega'] at this
  intro delta
  induction delta with
  | zero => intro; rfl
  | succ d IH =>
    intro LT
    have IH' := IH (by omega')
    have NOTSCHED : scheduled_at sched j (b + d) = false := by
      cases hs : scheduled_at sched j (b + d)
      · rfl
      · exfalso
        apply H_respects_self_suspensions j (b + d) hs
        have NC : completed_by job_cost sched j (b + d) = false := by
          cases hc : completed_by job_cost sched j (b + d)
          · rfl
          · have := completed_implies_not_scheduled job_cost sched j H_completed_jobs_dont_execute (b + d) hc
            rw [hs] at this; simp at this
        have TALE : time_after_last_execution job_arrival sched j (b + d) = b := by
          rw [same_service_implies_same_last_execution job_arrival sched j (b + d) b IH', IDEM]
        unfold suspended_at suspension_duration
        rw [NC, TALE]
        simp only [Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
        constructor <;> omega'
    unfold service service_during
    rw [show b + (d + 1) = (b + d) + 1 by omega', Finset.sum_Ico_succ_top (Nat.zero_le _)]
    unfold service service_during at IH'
    simp only [service_at, NOTSCHED, Bool.toNat_false, Nat.add_zero]
    exact IH'

theorem suspended_in_suspension_interval {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (j : Job) (t t_in : time) (H_not_completed : (!completed_by job_cost sched j t_in) = true)
    (H_within_suspension_interval :
      (decide (time_after_last_execution job_arrival sched j t ≤ t_in) &&
        decide (t_in < time_after_last_execution job_arrival sched j t +
          suspension_duration job_arrival next_suspension sched j t)) = true) :
    suspended_at job_arrival job_cost next_suspension sched j t_in = true := by
  have BETWEEN := H_within_suspension_interval
  simp only [Bool.and_eq_true, decide_eq_true_eq] at BETWEEN
  obtain ⟨GE, LT⟩ := BETWEEN
  have SERV := same_service_in_suspension_interval job_arrival job_cost next_suspension sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j t t_in
    (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
  have SAME : time_after_last_execution job_arrival sched j t = time_after_last_execution job_arrival sched j t_in := by
    rw [same_service_implies_same_last_execution job_arrival sched j t_in _ SERV,
      last_execution_idempotent job_arrival sched H_jobs_must_arrive_to_execute j t]
  unfold suspended_at
  rw [H_not_completed, Bool.true_and]
  unfold suspension_duration at LT ⊢
  rw [← SAME]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨GE, LT⟩

theorem suspended_implies_arrived {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (j : Job) (t : time)
    (H_j_is_suspended : suspended_at job_arrival job_cost next_suspension sched j t = true) :
    has_arrived job_arrival j t = true := by
  unfold suspended_at at H_j_is_suspended
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H_j_is_suspended
  have ARR := last_execution_after_arrival job_arrival sched H_jobs_must_arrive_to_execute j t
  simp only [has_arrived, decide_eq_true_eq] at ARR ⊢
  omega'

theorem suspended_implies_not_completed {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (j : Job) (t : time)
    (H_j_is_suspended : suspended_at job_arrival job_cost next_suspension sched j t = true) :
    (!completed_by job_cost sched j t) = true := by
  unfold suspended_at at H_j_is_suspended
  simp only [Bool.and_eq_true] at H_j_is_suspended
  exact H_j_is_suspended.1

/-- LEAN_HELPER: the suspended instants of a set, grouped by the service received so far. -/
private theorem suspended_decomposition {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job) (j : Job) (T : Finset Nat) :
    ∑ t ∈ T, (suspended_at job_arrival job_cost next_suspension sched j t).toNat =
      ∑ s ∈ Finset.Ico 0 (job_cost j), (T.filter (fun t => service sched j t = s ∧
        suspended_at job_arrival job_cost next_suspension sched j t = true)).card := by
  simp only [Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  cases hs : suspended_at job_arrival job_cost next_suspension sched j t
  · simp
  · have NC := suspended_implies_not_completed job_arrival job_cost next_suspension sched j t hs
    simp only [completed_by, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at NC
    simp only [and_true, Bool.toNat_true]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_Ico, Nat.zero_le, true_and]
    rw [if_pos NC]

theorem cumulative_suspension_le_total_suspension {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (next_suspension : job_suspension Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (j : Job) :
    ∀ t1 t2 : time, cumulative_suspension_during job_arrival job_cost next_suspension sched j t1 t2 ≤
      total_suspension job_cost next_suspension j := by
  intro t1 t2
  unfold cumulative_suspension_during total_suspension
  rw [suspended_decomposition]
  apply Finset.sum_le_sum
  intro s _
  rcases Finset.eq_empty_or_nonempty ((Finset.Ico t1 t2).filter (fun t => service sched j t = s ∧
      suspended_at job_arrival job_cost next_suspension sched j t = true)) with h | ⟨t', ht'⟩
  · rw [h]; exact Nat.zero_le _
  · rw [Finset.mem_filter] at ht'
    obtain ⟨_, SERV', _⟩ := ht'
    calc _ ≤ (Finset.Ico (time_after_last_execution job_arrival sched j t')
              (time_after_last_execution job_arrival sched j t' + next_suspension j s)).card := by
          apply Finset.card_le_card
          intro x hx
          rw [Finset.mem_filter] at hx
          obtain ⟨_, SERVx, SUSPx⟩ := hx
          unfold suspended_at suspension_duration at SUSPx
          simp only [Bool.and_eq_true, decide_eq_true_eq] at SUSPx
          obtain ⟨_, GEx, LTx⟩ := SUSPx
          rw [same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j x, SERVx]
            at LTx
          have SAME := same_service_implies_same_last_execution job_arrival sched j x t' (SERVx.trans SERV'.symm)
          rw [SAME] at GEx LTx
          rw [Finset.mem_Ico]; exact ⟨GEx, LTx⟩
      _ = next_suspension j s := by simp

theorem cumulative_suspension_eq_total_suspension {Job : Type u} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (next_suspension : job_suspension Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (j : Job) (t : time) (H_j_has_completed : completed_by job_cost sched j t = true) :
    cumulative_suspension job_arrival job_cost next_suspension sched j t =
      total_suspension job_cost next_suspension j := by
  apply Nat.le_antisymm
  · exact cumulative_suspension_le_total_suspension job_arrival job_cost next_suspension sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j 0 t
  unfold cumulative_suspension cumulative_suspension_during total_suspension
  rw [suspended_decomposition]
  apply Finset.sum_le_sum
  intro s hs
  rw [Finset.mem_Ico] at hs
  obtain ⟨t', EQ'⟩ := exists_last_execution_with_smaller_service job_arrival job_cost sched
    H_jobs_must_arrive_to_execute j t H_j_has_completed s hs.2
  calc next_suspension j s = (Finset.Ico (time_after_last_execution job_arrival sched j t')
        (time_after_last_execution job_arrival sched j t' + next_suspension j s)).card := by simp
    _ ≤ _ := by
      apply Finset.card_le_card
      intro i hi
      rw [Finset.mem_Ico] at hi
      have DUR : suspension_duration job_arrival next_suspension sched j t' = next_suspension j s := by
        unfold suspension_duration; rw [EQ']
      have SERVi := same_service_in_suspension_interval job_arrival job_cost next_suspension sched
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j t' i
        (by rw [DUR]; simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
      rw [EQ'] at SERVi
      have NC : (!completed_by job_cost sched j i) = true := by
        simp only [completed_by, SERVi, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le]
        exact hs.2
      have SUSPi := suspended_in_suspension_interval job_arrival job_cost next_suspension sched
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j t' i NC
        (by rw [DUR]; simp only [Bool.and_eq_true, decide_eq_true_eq]; exact hi)
      have LTi : i < t := by
        by_contra hc
        have := completion_monotonic job_cost sched j t i (by omega') H_j_has_completed
        rw [this] at NC; exact Bool.noConfusion NC
      rw [Finset.mem_filter, Finset.mem_Ico]
      exact ⟨⟨Nat.zero_le _, LTi⟩, SERVi, SUSPi⟩

theorem executes_before_suspension {Job : Type u} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (next_suspension : job_suspension Job) (sched : schedule Job)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (j : Job) (t : time) (H_arrived : has_arrived job_arrival j t = true)
    (H_not_suspended_at_t : (!suspended_at job_arrival job_cost next_suspension sched j t) = true)
    (H_begins_suspension : suspended_at job_arrival job_cost next_suspension sched j (t + 1) = true) :
    scheduled_at sched j t = true := by
  have SUSPs' := H_begins_suspension
  unfold suspended_at at SUSPs'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at SUSPs'
  obtain ⟨NOTCOMP', GE, LT⟩ := SUSPs'
  cases hs : scheduled_at sched j t
  · exfalso
    have SAMESERV : service sched j (t + 1) = service sched j t := by
      unfold service service_during
      rw [Finset.sum_Ico_succ_top (Nat.zero_le _)]
      simp [service_at, hs]
    have SAME := same_service_implies_same_last_execution job_arrival sched j (t + 1) t SAMESERV
    have BOUND := last_execution_bounded_by_identity job_arrival sched j t H_arrived
    have NC : (!completed_by job_cost sched j t) = true := by
      cases hc : completed_by job_cost sched j t
      · rfl
      · have := completion_monotonic job_cost sched j t (t + 1) (Nat.le_succ _) hc
        rw [this] at NOTCOMP'; exact absurd NOTCOMP' (by decide)
    have SUSP := suspended_in_suspension_interval job_arrival job_cost next_suspension sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions j (t + 1) t NC
      (by simp only [Bool.and_eq_true, decide_eq_true_eq]; constructor <;> omega')
    rw [SUSP] at H_not_suspended_at_t
    exact Bool.noConfusion H_not_suspended_at_t
  · rfl

end Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals
