-- Translated from: ../rt-proofs/classic/model/schedule/uni/susp/suspension_intervals.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution
open Classical

noncomputable section

section DefiningSuspensionIntervals

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (next_suspension : job_suspension Job)
variable (sched : schedule Job)

section JobSuspension

variable (j : Job)

section DefiningSuspension

variable (t : Time)

def suspension_duration : Duration :=
  next_suspension j (service sched j (time_after_last_execution job_arrival sched j t))

def suspended_at : Prop :=
  ¬ completed_by job_cost sched j t ∧
  (time_after_last_execution job_arrival sched j t ≤ t ∧
   t < time_after_last_execution job_arrival sched j t + suspension_duration job_arrival next_suspension sched j t)

end DefiningSuspension

def cumulative_suspension_during (t1 t2 : Time) : Nat :=
  Finset.sum (Finset.Ico t1 t2) (fun t => if suspended_at job_arrival job_cost next_suspension sched j t then 1 else 0)

def cumulative_suspension (t : Time) : Nat :=
  cumulative_suspension_during job_arrival job_cost next_suspension sched j 0 t

end JobSuspension

section SuspensionAwareSchedule

def respects_self_suspensions : Prop :=
  ∀ j t, scheduled_at sched j t = true →
    ¬ suspended_at job_arrival job_cost next_suspension sched j t

end SuspensionAwareSchedule

section Lemmas

section InsideSuspensionInterval

variable (j : Job)
variable (t : Time)

section SameService

variable (t_in : Time)

theorem same_service_in_suspension_interval
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (H_has_arrived : has_arrived job_arrival j t)
    (H_within_suspension_interval :
      time_after_last_execution job_arrival sched j t ≤ t_in ∧
      t_in ≤ time_after_last_execution job_arrival sched j t +
        suspension_duration job_arrival next_suspension sched j t) :
    service sched j t_in =
    service sched j (time_after_last_execution job_arrival sched j t) := by
  obtain ⟨hGE, hLE⟩ := H_within_suspension_interval
  suffices h_main : ∀ (d : Nat), d ≤ suspension_duration job_arrival next_suspension sched j t →
      service sched j (time_after_last_execution job_arrival sched j t + d) =
      service sched j (time_after_last_execution job_arrival sched j t) by
    have hd_le : t_in - time_after_last_execution job_arrival sched j t ≤
        suspension_duration job_arrival next_suspension sched j t :=
      Nat.sub_le_of_le_add (Nat.add_comm _ _ ▸ hLE)
    have := h_main (t_in - time_after_last_execution job_arrival sched j t) hd_le
    rwa [Nat.add_sub_cancel' hGE] at this
  intro d
  induction d with
  | zero => intro _; simp
  | succ n ih =>
    intro hnd
    have hnd' : n ≤ suspension_duration job_arrival next_suspension sched j t := Nat.le_of_succ_le hnd
    have ih' := ih hnd'
    have h_not_sched : ¬ (scheduled_at sched j (time_after_last_execution job_arrival sched j t + n) = true) := by
      intro hsched
      apply H_respects_self_suspensions j _ hsched
      have h_same_le : time_after_last_execution job_arrival sched j (time_after_last_execution job_arrival sched j t + n) = time_after_last_execution job_arrival sched j t := by
        rw [same_service_implies_same_last_execution job_arrival sched H_jobs_must_arrive_to_execute j _ _ ih']
        exact last_execution_idempotent job_arrival sched H_jobs_must_arrive_to_execute j t
      refine ⟨?_, ?_, ?_⟩
      · intro hcomp
        exact (completed_implies_not_scheduled job_cost sched j H_completed_jobs_dont_execute _ hcomp) hsched
      · rw [h_same_le]; exact Nat.le_add_right _ _
      · simp only [suspension_duration]; rw [h_same_le]
        exact Nat.add_lt_add_left (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (Nat.le_refl n)) hnd) _
    have h_serv_succ : service sched j (time_after_last_execution job_arrival sched j t + (n + 1)) =
        service sched j (time_after_last_execution job_arrival sched j t + n) +
        service_at sched j (time_after_last_execution job_arrival sched j t + n) := by
      unfold service service_during
      conv_lhs => rw [show time_after_last_execution job_arrival sched j t + (n + 1) =
          (time_after_last_execution job_arrival sched j t + n) + 1 from Nat.add_succ _ _]
      rw [← Finset.sum_Ico_succ_top (show (0 : Nat) ≤ time_after_last_execution job_arrival sched j t + n from Nat.zero_le _)]
    rw [h_serv_succ, ih']
    unfold service_at
    have h_false : scheduled_at sched j (time_after_last_execution job_arrival sched j t + n) = false :=
      Bool.eq_false_of_not_eq_true h_not_sched
    simp [h_false]

end SameService

section JobSuspendedAtAllTimes

variable (t_in : Time)

theorem suspended_in_suspension_interval
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (H_has_arrived : has_arrived job_arrival j t)
    (H_not_completed : ¬ completed_by job_cost sched j t_in)
    (H_within_suspension_interval :
      time_after_last_execution job_arrival sched j t ≤ t_in ∧
      t_in < time_after_last_execution job_arrival sched j t +
        suspension_duration job_arrival next_suspension sched j t) :
    suspended_at job_arrival job_cost next_suspension sched j t_in := by
  obtain ⟨hGE, hLT⟩ := H_within_suspension_interval
  set b := time_after_last_execution job_arrival sched j t with hb_def
  set dur := suspension_duration job_arrival next_suspension sched j t with hdur_def
  have hARR : has_arrived job_arrival j t_in :=
    Nat.le_trans (last_execution_after_arrival job_arrival sched H_jobs_must_arrive_to_execute j t) hGE
  -- Show same service, hence same last execution
  have hSameServ : service sched j t_in = service sched j b :=
    same_service_in_suspension_interval job_arrival job_cost next_suspension sched j t t_in
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions
      H_has_arrived ⟨hGE, Nat.le_of_lt hLT⟩
  have hSAME : time_after_last_execution job_arrival sched j t =
               time_after_last_execution job_arrival sched j t_in := by
    rw [same_service_implies_same_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t_in b hSameServ]
    exact (last_execution_idempotent job_arrival sched H_jobs_must_arrive_to_execute j t).symm
  refine ⟨H_not_completed, last_execution_bounded_by_identity job_arrival sched H_jobs_must_arrive_to_execute j t_in hARR, ?_⟩
  -- t_in < time_after_last_execution ... t_in + suspension_duration ... t_in
  calc t_in < b + dur := hLT
    _ = time_after_last_execution job_arrival sched j t_in +
        next_suspension j (service sched j (time_after_last_execution job_arrival sched j t_in)) := by
      rw [← hSAME]
      simp only [suspension_duration] at hdur_def
      rw [← hdur_def, ← hb_def]

end JobSuspendedAtAllTimes

end InsideSuspensionInterval

section StateOfSuspendedJob

variable (j : Job)
variable (t : Time)

theorem suspended_implies_arrived
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_j_is_suspended : suspended_at job_arrival job_cost next_suspension sched j t) :
    has_arrived job_arrival j t := by
  obtain ⟨_, hle, _⟩ := H_j_is_suspended
  exact Nat.le_trans (last_execution_after_arrival job_arrival sched H_jobs_must_arrive_to_execute j t) hle

theorem suspended_implies_not_completed
    (H_j_is_suspended : suspended_at job_arrival job_cost next_suspension sched j t) :
    ¬ completed_by job_cost sched j t := by
  exact H_j_is_suspended.1

end StateOfSuspendedJob

section BoundOnCumulativeSuspension

variable (j : Job)

theorem cumulative_suspension_le_total_suspension
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched) :
    ∀ t1 t2,
      cumulative_suspension_during job_arrival job_cost next_suspension sched j t1 t2 ≤
      total_suspension job_cost next_suspension j := by
  intro t1 t2
  unfold cumulative_suspension_during total_suspension
  -- We bound ∑_{t ∈ [t1,t2)} indicator(t) ≤ ∑_{s < job_cost j} next_suspension j s
  -- by partitioning suspended times by service level.
  -- Step 1: bound indicator sum by double sum partitioned by service level
  have h_step1 :
      ∑ t ∈ Finset.Ico t1 t2,
        (if suspended_at job_arrival job_cost next_suspension sched j t then 1 else 0) ≤
      ∑ s ∈ Finset.range (job_cost j),
        ((Finset.Ico t1 t2).filter (fun t =>
          suspended_at job_arrival job_cost next_suspension sched j t ∧
          service sched j (time_after_last_execution job_arrival sched j t) = s)).card := by
    -- The LHS equals the cardinality of the suspended filter
    have h_lhs : ∑ t ∈ Finset.Ico t1 t2,
        (if suspended_at job_arrival job_cost next_suspension sched j t then 1 else 0) =
        ((Finset.Ico t1 t2).filter (suspended_at job_arrival job_cost next_suspension sched j)).card := by
      rw [← Finset.sum_filter]
      rw [Finset.card_eq_sum_ones]
    rw [h_lhs]
    -- The RHS equals the cardinality of the biUnion of the partitions
    have h_rhs :
        ∑ s ∈ Finset.range (job_cost j),
          ((Finset.Ico t1 t2).filter (fun t =>
            suspended_at job_arrival job_cost next_suspension sched j t ∧
            service sched j (time_after_last_execution job_arrival sched j t) = s)).card =
        ((Finset.range (job_cost j)).biUnion (fun s =>
          (Finset.Ico t1 t2).filter (fun t =>
            suspended_at job_arrival job_cost next_suspension sched j t ∧
            service sched j (time_after_last_execution job_arrival sched j t) = s))).card := by
      rw [Finset.card_biUnion]
      intro s₁ _ s₂ _ hne
      apply Finset.disjoint_filter.mpr
      intro t _ ⟨_, hs₁⟩ ⟨_, hs₂⟩
      exact hne (hs₁.symm ▸ hs₂)
    rw [h_rhs]
    apply Finset.card_le_card
    intro t ht
    simp only [Finset.mem_filter] at ht
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range]
    obtain ⟨ht_mem, hsusp⟩ := ht
    have h_same := same_service_since_last_execution job_arrival sched
      H_jobs_must_arrive_to_execute j t
    have h_serv_lt : service sched j (time_after_last_execution job_arrival sched j t) < job_cost j := by
      rw [h_same]; exact Nat.lt_of_not_le (fun hle' => hsusp.1 hle')
    exact ⟨_, h_serv_lt, ht_mem, hsusp, rfl⟩
  -- Step 2: bound each partition by next_suspension j s
  have h_step2 :
      ∑ s ∈ Finset.range (job_cost j),
        ((Finset.Ico t1 t2).filter (fun t =>
          suspended_at job_arrival job_cost next_suspension sched j t ∧
          service sched j (time_after_last_execution job_arrival sched j t) = s)).card ≤
      ∑ s ∈ Finset.range (job_cost j), next_suspension j s := by
    apply Finset.sum_le_sum
    intro s _
    -- All suspended times t with service level s share the same time_after_last_execution,
    -- so they all lie in a single interval of length next_suspension j s.
    by_cases h_empty : ((Finset.Ico t1 t2).filter (fun t =>
      suspended_at job_arrival job_cost next_suspension sched j t ∧
      service sched j (time_after_last_execution job_arrival sched j t) = s)).Nonempty
    · obtain ⟨t', ht'⟩ := h_empty
      simp only [Finset.mem_filter, Finset.mem_Ico] at ht'
      obtain ⟨⟨_, _⟩, hsusp', hserv'⟩ := ht'
      set b' := time_after_last_execution job_arrival sched j t'
      -- Show filter ⊆ Finset.Ico b' (b' + next_suspension j s)
      have h_sub : (Finset.Ico t1 t2).filter (fun t =>
          suspended_at job_arrival job_cost next_suspension sched j t ∧
          service sched j (time_after_last_execution job_arrival sched j t) = s) ⊆
          Finset.Ico b' (b' + next_suspension j s) := by
        intro t ht_mem
        simp only [Finset.mem_filter, Finset.mem_Ico] at ht_mem ⊢
        obtain ⟨⟨_, _⟩, hsusp_t, hserv_t⟩ := ht_mem
        obtain ⟨_, hle_t, hlt_t⟩ := hsusp_t
        have h_idem_t := last_execution_idempotent job_arrival sched
          H_jobs_must_arrive_to_execute j t
        have h_idem_t' := last_execution_idempotent job_arrival sched
          H_jobs_must_arrive_to_execute j t'
        have h_same_b : time_after_last_execution job_arrival sched j t = b' := by
          have := same_service_implies_same_last_execution job_arrival sched
            H_jobs_must_arrive_to_execute j
            (time_after_last_execution job_arrival sched j t)
            (time_after_last_execution job_arrival sched j t')
            (by rw [hserv_t, hserv'])
          rw [h_idem_t, h_idem_t'] at this
          exact this
        rw [← h_same_b]
        refine ⟨hle_t, ?_⟩
        simp only [suspension_duration] at hlt_t
        rw [hserv_t] at hlt_t
        exact hlt_t
      calc ((Finset.Ico t1 t2).filter (fun t =>
              suspended_at job_arrival job_cost next_suspension sched j t ∧
              service sched j (time_after_last_execution job_arrival sched j t) = s)).card
          ≤ (Finset.Ico b' (b' + next_suspension j s)).card := Finset.card_le_card h_sub
        _ = next_suspension j s := by rw [Nat.card_Ico]; exact Nat.add_sub_cancel_left b' (next_suspension j s)
    · rw [Finset.not_nonempty_iff_eq_empty.mp h_empty]
      exact Finset.card_empty ▸ Nat.zero_le _
  exact le_trans h_step1 h_step2

end BoundOnCumulativeSuspension

section SuspendsForTotalSuspension

variable (j : Job)
variable (t : Time)

theorem cumulative_suspension_eq_total_suspension
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (H_j_has_completed : completed_by job_cost sched j t) :
    cumulative_suspension job_arrival job_cost next_suspension sched j t =
    total_suspension job_cost next_suspension j := by
  apply Nat.le_antisymm
  · -- ≤ direction: from cumulative_suspension_le_total_suspension
    exact cumulative_suspension_le_total_suspension job_arrival job_cost next_suspension sched j
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions 0 t
  · -- ≥ direction: total_suspension ≤ cumulative_suspension
    unfold cumulative_suspension cumulative_suspension_during total_suspension
    -- We need: ∑_{s < job_cost j} next_suspension j s ≤ ∑_{i ∈ [0,t)} indicator(i)
    -- For each s < job_cost j, we show next_suspension j s ≤ count of suspended times in [0,t) with service level s
    -- Step: bound total_suspension by a double sum
    -- ∑_{s < cost} next_suspension j s ≤ ∑_{s < cost} ∑_{i ∈ [0,t) | suspended ∧ service = s} 1
    -- ≤ ∑_{i ∈ [0,t)} indicator(i) (by partition)
    -- For the ≥ direction, we show: ∑_{s < cost} next_suspension j s ≤ ∑_{i ∈ [0,t)} indicator(i)
    -- Each next_suspension j s is bounded by the count of suspended times with that service level.
    -- The key helper: for each i in a suspension interval, it's suspended, not completed, and has service = s.
    -- We first prove a helper to avoid repetition:
    have h_in_interval : ∀ (s : ℕ) (t' : Time),
        service sched j (time_after_last_execution job_arrival sched j t') = s →
        s < job_cost j →
        ∀ i, time_after_last_execution job_arrival sched j t' ≤ i →
             i < time_after_last_execution job_arrival sched j t' + next_suspension j s →
             i < t ∧ suspended_at job_arrival job_cost next_suspension sched j i ∧
             service sched j (time_after_last_execution job_arrival sched j i) = s := by
      intro s₀ t₀ hserv₀ hs_lt i hle_i hlt_i
      -- Use b₀ = time_after_last_execution j t₀ as pivot
      set b₀ := time_after_last_execution job_arrival sched j t₀ with hb₀_def
      have h_arr_b₀ : has_arrived job_arrival j b₀ :=
        last_execution_after_arrival job_arrival sched H_jobs_must_arrive_to_execute j t₀
      have h_idem := last_execution_idempotent job_arrival sched H_jobs_must_arrive_to_execute j t₀
      -- suspension_duration j b₀ = next_suspension j (service j (b(b₀))) = next_suspension j (service j b₀) = next_suspension j s₀
      have h_susp_dur : suspension_duration job_arrival next_suspension sched j b₀ = next_suspension j s₀ := by
        unfold suspension_duration; rw [h_idem, hserv₀]
      -- time_after_last_execution j b₀ = b₀
      -- The interval [b₀, b₀ + next_suspension j s₀) = [b(b₀), b(b₀) + suspension_duration j b₀)
      -- same_service_in_suspension_interval with pivot b₀:
      have h_within_le : b₀ ≤ i ∧ i ≤ b₀ + suspension_duration job_arrival next_suspension sched j b₀ := by
        rw [h_susp_dur]; exact ⟨hle_i, Nat.le_of_lt hlt_i⟩
      -- Rewrite using idem: time_after_last_execution j b₀ = b₀
      have h_within_le' : time_after_last_execution job_arrival sched j b₀ ≤ i ∧
          i ≤ time_after_last_execution job_arrival sched j b₀ +
            suspension_duration job_arrival next_suspension sched j b₀ := by
        rw [h_idem]; exact h_within_le
      have h_same_serv := same_service_in_suspension_interval job_arrival job_cost next_suspension sched
        j b₀ i H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions
        h_arr_b₀ h_within_le'
      rw [h_idem, hserv₀] at h_same_serv
      -- service j i = s₀ < job_cost j, so not completed
      have h_not_comp : ¬ completed_by job_cost sched j i := by
        intro hcomp
        have h_lt : service sched j i < job_cost j := h_same_serv ▸ hs_lt
        exact Nat.not_le.mpr h_lt hcomp
      -- i < t: by contradiction, if i ≥ t then completed at i (contradiction)
      have h_i_lt_t : i < t := by
        by_contra h_ge; push_neg at h_ge
        exact h_not_comp (completion_monotonic job_cost sched j t i h_ge H_j_has_completed)
      -- Show suspended at i using suspended_in_suspension_interval with pivot b₀
      have h_within_lt : time_after_last_execution job_arrival sched j b₀ ≤ i ∧
          i < time_after_last_execution job_arrival sched j b₀ +
            suspension_duration job_arrival next_suspension sched j b₀ := by
        rw [h_idem, h_susp_dur]; exact ⟨hle_i, hlt_i⟩
      have h_susp := suspended_in_suspension_interval job_arrival job_cost next_suspension sched j b₀ i
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_respects_self_suspensions
        h_arr_b₀ h_not_comp h_within_lt
      -- Show service j (b(i)) = s₀
      have h_serv_eq_b : service sched j i = service sched j b₀ := by
        rw [h_same_serv, ← hserv₀]
      have h_same_last := same_service_implies_same_last_execution job_arrival sched
        H_jobs_must_arrive_to_execute j i b₀ h_serv_eq_b
      refine ⟨h_i_lt_t, h_susp, ?_⟩
      rw [h_same_last, h_idem, hserv₀]
    -- Now the main calc chain for ≥
    -- Strategy: ∑_{s} n_s ≤ ∑_{s} card(filter_s) = card(⋃ filter_s) ≤ ∑_{i} indicator
    -- where filter_s = {i ∈ [0,t) | suspended(i) ∧ service(b(i)) = s}
    -- Step A: ∑_{s} n_s ≤ ∑_{s} card(filter_s)
    have h_step_a : ∑ s ∈ Finset.range (job_cost j), next_suspension j s ≤
        ∑ s ∈ Finset.range (job_cost j),
          ((Finset.Ico 0 t).filter (fun i =>
            suspended_at job_arrival job_cost next_suspension sched j i ∧
            service sched j (time_after_last_execution job_arrival sched j i) = s)).card := by
      apply Finset.sum_le_sum
      intro s hs
      rw [Finset.mem_range] at hs
      obtain ⟨t', hserv'⟩ := exists_last_execution_with_smaller_service job_arrival job_cost sched
        H_jobs_must_arrive_to_execute j t H_j_has_completed s hs
      set b' := time_after_last_execution job_arrival sched j t'
      -- Ico b' (b' + n) ⊆ filter, and card of Ico = n
      have h_sub : Finset.Ico b' (b' + next_suspension j s) ⊆
          (Finset.Ico 0 t).filter (fun i =>
            suspended_at job_arrival job_cost next_suspension sched j i ∧
            service sched j (time_after_last_execution job_arrival sched j i) = s) := by
        intro i hi
        simp only [Finset.mem_Ico] at hi
        simp only [Finset.mem_filter, Finset.mem_Ico]
        obtain ⟨hle_i, hlt_i⟩ := hi
        obtain ⟨h_lt, h_susp, h_serv⟩ := h_in_interval s t' hserv' hs i hle_i hlt_i
        exact ⟨⟨Nat.zero_le _, h_lt⟩, h_susp, h_serv⟩
      have h_card_ico : (Finset.Ico b' (b' + next_suspension j s)).card = next_suspension j s := by
        rw [Nat.card_Ico]; omega
      calc next_suspension j s
            = (Finset.Ico b' (b' + next_suspension j s)).card := h_card_ico.symm
          _ ≤ ((Finset.Ico 0 t).filter (fun i =>
                suspended_at job_arrival job_cost next_suspension sched j i ∧
                service sched j (time_after_last_execution job_arrival sched j i) = s)).card :=
              Finset.card_le_card h_sub
    -- Step B: ∑_{s} card(filter_s) = card(⋃ filter_s) (disjoint union)
    have h_disjoint : ∀ s₁ ∈ Finset.range (job_cost j), ∀ s₂ ∈ Finset.range (job_cost j), s₁ ≠ s₂ →
        Disjoint ((Finset.Ico 0 t).filter (fun i =>
            suspended_at job_arrival job_cost next_suspension sched j i ∧
            service sched j (time_after_last_execution job_arrival sched j i) = s₁))
          ((Finset.Ico 0 t).filter (fun i =>
            suspended_at job_arrival job_cost next_suspension sched j i ∧
            service sched j (time_after_last_execution job_arrival sched j i) = s₂)) := by
      intro s₁ _ s₂ _ hne
      apply Finset.disjoint_filter.mpr
      intro i _ ⟨_, hs₁⟩ ⟨_, hs₂⟩
      exact hne (hs₁.symm ▸ hs₂)
    have h_step_b : ∑ s ∈ Finset.range (job_cost j),
        ((Finset.Ico 0 t).filter (fun i =>
          suspended_at job_arrival job_cost next_suspension sched j i ∧
          service sched j (time_after_last_execution job_arrival sched j i) = s)).card =
        ((Finset.range (job_cost j)).biUnion (fun s =>
          (Finset.Ico 0 t).filter (fun i =>
            suspended_at job_arrival job_cost next_suspension sched j i ∧
            service sched j (time_after_last_execution job_arrival sched j i) = s))).card := by
      exact (Finset.card_biUnion h_disjoint).symm
    -- Step C: card(⋃ filter_s) ≤ ∑_{i ∈ [0,t)} indicator(i)
    have h_step_c : ((Finset.range (job_cost j)).biUnion (fun s =>
        (Finset.Ico 0 t).filter (fun i =>
          suspended_at job_arrival job_cost next_suspension sched j i ∧
          service sched j (time_after_last_execution job_arrival sched j i) = s))).card ≤
        ∑ i ∈ Finset.Ico 0 t,
          (if suspended_at job_arrival job_cost next_suspension sched j i then 1 else 0) := by
      -- biUnion ⊆ {i ∈ [0,t) | suspended(i)}, and card of that = ∑ indicator
      have h_union_sub : (Finset.range (job_cost j)).biUnion (fun s =>
          (Finset.Ico 0 t).filter (fun i =>
            suspended_at job_arrival job_cost next_suspension sched j i ∧
            service sched j (time_after_last_execution job_arrival sched j i) = s)) ⊆
          (Finset.Ico 0 t).filter (suspended_at job_arrival job_cost next_suspension sched j) := by
        intro i hi
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_range] at hi
        obtain ⟨_, _, hmem, hsusp, _⟩ := hi
        simp only [Finset.mem_filter]; exact ⟨hmem, hsusp⟩
      calc ((Finset.range (job_cost j)).biUnion _).card
          ≤ ((Finset.Ico 0 t).filter (suspended_at job_arrival job_cost next_suspension sched j)).card :=
            Finset.card_le_card h_union_sub
        _ = ∑ i ∈ Finset.Ico 0 t,
              (if suspended_at job_arrival job_cost next_suspension sched j i then 1 else 0) := by
            rw [← Finset.sum_filter]; rw [Finset.card_eq_sum_ones]
    exact le_trans (le_trans h_step_a (h_step_b ▸ le_refl _)) h_step_c

end SuspendsForTotalSuspension

section ExecutionBeforeSuspension

variable (j : Job)
variable (t : Time)

theorem executes_before_suspension
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (H_arrived : has_arrived job_arrival j t)
    (H_not_suspended_at_t : ¬ suspended_at job_arrival job_cost next_suspension sched j t)
    (H_begins_suspension : suspended_at job_arrival job_cost next_suspension sched j (t + 1)) :
    scheduled_at sched j t = true := by
  obtain ⟨hNotComp', hGE', hLT'⟩ := H_begins_suspension
  by_contra hNotSched
  -- If j is not scheduled at t, then time_after_last_execution at t+1 = time_after_last_execution at t
  -- because service at t+1 = service at t (no scheduling at t means service_at t = 0)
  have h_same_serv : service sched j (t + 1) = service sched j t := by
    unfold service service_during
    have hsplit : ∑ x ∈ Finset.Ico 0 (t + 1), service_at sched j x =
        ∑ x ∈ Finset.Ico 0 t, service_at sched j x + service_at sched j t := by
      rw [← Finset.sum_Ico_succ_top (show (0 : Nat) ≤ t from Nat.zero_le _)]
    rw [hsplit]
    have : service_at sched j t = 0 := by
      unfold service_at scheduled_at at hNotSched ⊢
      rw [Bool.not_eq_true] at hNotSched; simp [hNotSched]
    omega
  -- Hence same last execution
  have h_same_last := same_service_implies_same_last_execution job_arrival sched H_jobs_must_arrive_to_execute j (t + 1) t h_same_serv
  -- j is not completed at t (otherwise it would be completed at t+1, contradicting hNotComp')
  have hNotComp : ¬ completed_by job_cost sched j t := by
    intro hcomp
    exact hNotComp' (completion_monotonic job_cost sched j t (t + 1) (Nat.le_succ _) hcomp)
  -- j is suspended at t, contradiction
  apply H_not_suspended_at_t
  constructor
  · exact hNotComp
  · constructor
    · -- time_after_last_execution j t ≤ t
      exact last_execution_bounded_by_identity job_arrival sched H_jobs_must_arrive_to_execute j t H_arrived
    · -- t < time_after_last_execution j t + suspension_duration j t
      have hsd_eq : suspension_duration job_arrival next_suspension sched j (t + 1) =
          suspension_duration job_arrival next_suspension sched j t := by
        unfold suspension_duration; rw [h_same_last]
      rw [← h_same_last, ← hsd_eq]; exact Nat.lt_trans (Nat.lt_succ_of_le (le_refl t)) hLT'  

end ExecutionBeforeSuspension

end Lemmas

end DefiningSuspensionIntervals

end

end Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
