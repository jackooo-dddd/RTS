-- Translated from: ../rt-proofs/classic/model/schedule/uni/susp/build_suspension_table.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Susp.Build_suspension_table

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

noncomputable section

namespace SuspensionTableConstruction

section BuildingSuspensionTable

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (arr_seq : arrival_sequence Job)
variable (sched : schedule Job)
variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)

variable (t_max : Time)
variable (job_suspended_at : Job → Time → Bool)

variable (H_arrived :
  ∀ j t, t < t_max → job_suspended_at j t = true → has_arrived job_arrival j t)

variable (H_not_completed :
  ∀ j t, t < t_max → job_suspended_at j t = true → ¬ completed_by job_cost sched j t)

variable (H_continuous_suspension :
  ∀ j t t_susp,
    t < t_max →
    job_suspended_at j t = true →
    time_after_last_execution job_arrival sched j t ≤ t_susp ∧ t_susp < t →
    job_suspended_at j t_susp = true)

def build_suspension_duration (j : Job) (s : Time) : Duration :=
  ∑ t ∈ Finset.Ico 0 t_max |>.filter (fun t => service sched j t = s),
    (job_suspended_at j t).toNat

section HelperLemmas

include H_jobs_must_arrive_to_execute H_arrived H_not_completed H_continuous_suspension

include H_jobs_must_arrive_to_execute H_arrived H_not_completed H_continuous_suspension in
theorem not_suspended_before_suspension_start
    (j : Job) (t : Time)
    (h_lt : t < t_max)
    (h_susp : job_suspended_at j t = true) :
    let susp_start := time_after_last_execution job_arrival sched j t
    let S := service sched j
    ∑ i ∈ Finset.Ico 0 susp_start |>.filter (fun i => S i = S susp_start),
      (job_suspended_at j i).toNat = 0 := by
  simp only
  apply Finset.sum_eq_zero
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_Ico] at hi
  obtain ⟨⟨_, hi_lt⟩, hserv_eq⟩ := hi
  cases h_case : job_suspended_at j i with
  | false => simp [Bool.toNat]
  | true =>
    exfalso
    have h_le_t : time_after_last_execution job_arrival sched j t ≤ t :=
      last_execution_bounded_by_identity job_arrival sched H_jobs_must_arrive_to_execute j t
        (H_arrived j t h_lt h_susp)
    have hi_lt_t : i < t := Nat.lt_of_lt_of_le hi_lt h_le_t
    have hi_lt_tmax : i < t_max := Nat.lt_trans hi_lt_t h_lt
    have h_arr_i : has_arrived job_arrival j i := H_arrived j i hi_lt_tmax h_case
    have h_less : service sched j i < service sched j t :=
      less_service_before_start_of_suspension job_arrival sched H_jobs_must_arrive_to_execute j t i
        h_arr_i hi_lt
    have h_same : service sched j (time_after_last_execution job_arrival sched j t) = service sched j t :=
      same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t
    rw [h_same] at hserv_eq
    omega

include H_jobs_must_arrive_to_execute H_arrived H_not_completed H_continuous_suspension in
theorem suspension_duration_no_suspension_after_t_max
    (j : Job) (t : Time)
    (h_arr : has_arrived job_arrival j t)
    (h_ge : t_max ≤ t) :
    ¬ suspended_at job_arrival job_cost
        (build_suspension_duration sched t_max job_suspended_at) sched j t := by
  intro ⟨h_not_comp, h_le_ex, h_lt_dur⟩
  -- h_lt_dur: t < time_after_last_execution ... j t + suspension_duration ...
  -- suspension_duration here = build_suspension_duration ... j (service sched j (time_after_last_execution ... j t))
  set ex := time_after_last_execution job_arrival sched j t with hex_def
  set S := service sched j with hS_def
  -- Unfold suspension_duration in h_lt_dur
  simp only [suspension_duration, build_suspension_duration] at h_lt_dur
  -- The sum is over (Finset.Ico 0 t_max).filter (fun t => S t = S ex)
  -- We show that ex + this sum ≤ t, contradicting h_lt_dur
  -- Helper: for any i < ex with S i = S ex, (job_suspended_at j i).toNat = 0
  have h_zero_before : ∀ i, i < ex → i < t_max → S i = S ex → (job_suspended_at j i).toNat = 0 := by
    intro i hi_lt hi_tmax hserv
    cases h_case : job_suspended_at j i with
    | false => simp [Bool.toNat]
    | true =>
      exfalso
      have h_arr_i : has_arrived job_arrival j i := H_arrived j i hi_tmax h_case
      have h_less : S i < S t :=
        less_service_before_start_of_suspension job_arrival sched H_jobs_must_arrive_to_execute j t i
          h_arr_i hi_lt
      have h_same : S ex = S t :=
        same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t
      omega
  -- The filtered sum over [0, t_max) with S i = S ex
  -- Split by whether ex < t_max or not
  by_cases h_ex_lt : ex < t_max
  · -- Case ex < t_max
    -- The sum = sum over [0, ex) filtered + sum over [ex, t_max) filtered
    -- Sum over [0, ex) filtered: each term is 0
    -- Sum over [ex, t_max) filtered: each term ≤ 1, and there are at most t_max - ex terms
    -- So total ≤ t_max - ex, hence ex + total ≤ t_max ≤ t
    have h_sum_le : ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
        (job_suspended_at j i).toNat ≤ t_max - ex := by
      -- Split the sum
      have h_filter_sub : (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex) ⊆
          (Finset.Ico 0 ex).filter (fun t_1 => S t_1 = S ex) ∪
          (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex) := by
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at hx ⊢
        obtain ⟨⟨hx0, hx_tmax⟩, hserv⟩ := hx
        by_cases hxex : x < ex
        · left; exact ⟨⟨hx0, hxex⟩, hserv⟩
        · right; push_neg at hxex; exact ⟨⟨hxex, hx_tmax⟩, hserv⟩
      calc ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat
          ≤ ∑ i ∈ (Finset.Ico 0 ex).filter (fun t_1 => S t_1 = S ex) ∪
                (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat := Finset.sum_le_sum_of_subset_of_nonneg h_filter_sub (fun i _ _ => Nat.zero_le _)
        _ ≤ ∑ i ∈ (Finset.Ico 0 ex).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat +
            ∑ i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat := by
          apply le_of_eq
          apply Finset.sum_union
          apply Finset.disjoint_filter_filter
          exact Finset.Ico_disjoint_Ico_consecutive 0 ex t_max
        _ ≤ 0 + ∑ i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat := by
          apply Nat.add_le_add_right
          apply Nat.le_of_eq
          apply Finset.sum_eq_zero
          intro i hi
          simp only [Finset.mem_filter, Finset.mem_Ico] at hi
          exact h_zero_before i hi.1.2 (Nat.lt_trans hi.1.2 h_ex_lt) hi.2
        _ ≤ t_max - ex := by
          simp only [Nat.zero_add]
          calc ∑ i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex),
                  (job_suspended_at j i).toNat
              ≤ ∑ i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex), 1 :=
                Finset.sum_le_sum (fun i _ => by cases job_suspended_at j i <;> simp [Bool.toNat])
            _ ≤ ∑ _i ∈ Finset.Ico ex t_max, 1 :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.filter_subset _ _) (fun i _ _ => Nat.zero_le _)
            _ = t_max - ex := by rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
    have h_ex_le_t : ex ≤ t :=
      last_execution_bounded_by_identity job_arrival sched H_jobs_must_arrive_to_execute j t h_arr
    have h_bound : ex + ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
        (job_suspended_at j i).toNat ≤ t := by
      calc ex + ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat
          ≤ ex + (t_max - ex) := Nat.add_le_add_left h_sum_le ex
        _ = t_max := Nat.add_sub_cancel' (Nat.le_of_lt h_ex_lt)
        _ ≤ t := h_ge
    -- Now h_lt_dur and h_bound contradict: t < ex + sum ≤ t
    -- But the sum in h_lt_dur may use different notation; let's convert
    change t < ex + ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
        (job_suspended_at j i).toNat at h_lt_dur
    exact Nat.not_lt.mpr h_bound h_lt_dur
  · -- Case ex ≥ t_max
    push_neg at h_ex_lt
    -- All terms in [0, t_max) with S i = S ex have i < t_max ≤ ex, so i < ex
    -- By h_zero_before, each term is 0
    have h_sum_zero : ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
        (job_suspended_at j i).toNat = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi
      exact h_zero_before i (Nat.lt_of_lt_of_le hi.1.2 h_ex_lt) hi.1.2 hi.2
    -- ex + 0 = ex ≤ t, contradicts h_lt_dur
    have h_ex_le_t : ex ≤ t :=
      last_execution_bounded_by_identity job_arrival sched H_jobs_must_arrive_to_execute j t h_arr
    rw [h_sum_zero, Nat.add_zero] at h_lt_dur
    exact Nat.not_lt.mpr h_ex_le_t h_lt_dur

end HelperLemmas

include H_jobs_must_arrive_to_execute H_arrived H_not_completed H_continuous_suspension

include H_jobs_must_arrive_to_execute H_arrived H_not_completed H_continuous_suspension in
theorem suspension_duration_matches_predicate_up_to_t_max
    (j : Job) (t : Time)
    (h_lt : t < t_max) :
    job_suspended_at j t = true ↔
    suspended_at job_arrival job_cost
      (build_suspension_duration sched t_max job_suspended_at) sched j t := by
  set ex := time_after_last_execution job_arrival sched j t with hex_def
  set S := service sched j with hS_def
  constructor
  · -- Forward
    intro hSUSPt
    have hARR : has_arrived job_arrival j t := H_arrived j t h_lt hSUSPt
    have hNCOMP : ¬ completed_by job_cost sched j t := H_not_completed j t h_lt hSUSPt
    have hEXle : ex ≤ t :=
      last_execution_bounded_by_identity job_arrival sched H_jobs_must_arrive_to_execute j t hARR
    refine ⟨hNCOMP, hEXle, ?_⟩
    simp only [suspension_duration, build_suspension_duration]
    have hSameServEx : S ex = S t :=
      same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t
    have hAllSusp : ∀ i, ex ≤ i → i ≤ t → job_suspended_at j i = true := by
      intro i hge hle
      rcases Nat.eq_or_lt_of_le hle with rfl | hilt
      · exact hSUSPt
      · exact H_continuous_suspension j t i h_lt hSUSPt ⟨hge, hilt⟩
    have hSameServ : ∀ i, ex ≤ i → i ≤ t → S i = S ex := by
      intro i hge hle
      have h1 : S ex ≤ S i := by
        simp only [hS_def, service, service_during]
        exact Finset.sum_le_sum_of_subset (fun x hx => by
          rw [Finset.mem_Ico] at hx ⊢; exact ⟨hx.1, Nat.lt_of_lt_of_le hx.2 hge⟩)
      have h2 : S i ≤ S t := by
        simp only [hS_def, service, service_during]
        exact Finset.sum_le_sum_of_subset (fun x hx => by
          rw [Finset.mem_Ico] at hx ⊢; exact ⟨hx.1, Nat.lt_of_lt_of_le hx.2 hle⟩)
      exact Nat.le_antisymm (hSameServEx ▸ h2) h1
    suffices h_sum_ge : t + 1 - ex ≤
        ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
          (job_suspended_at j i).toNat by
      have h_add : ex + (t + 1 - ex) ≤ ex + ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
          (job_suspended_at j i).toNat := Nat.add_le_add_left h_sum_ge ex
      rw [Nat.add_sub_cancel' (Nat.le_succ_of_le hEXle)] at h_add
      -- h_add : t + 1 ≤ ex + sum
      -- goal: t < ex + sum (which is the same)
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le (le_refl t)) h_add
    have hSubset : Finset.Ico ex (t + 1) ⊆
        (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      simp only [Finset.mem_filter, Finset.mem_Ico]
      have hle : i ≤ t := Nat.lt_succ_iff.mp hi.2
      exact ⟨⟨Nat.zero_le _, Nat.lt_of_le_of_lt hle h_lt⟩, hSameServ i hi.1 hle⟩
    calc t + 1 - ex
        = (Finset.Ico ex (t + 1)).card := by rw [Nat.card_Ico]
      _ = ∑ _i ∈ Finset.Ico ex (t + 1), 1 := by rw [Finset.card_eq_sum_ones]
      _ ≤ ∑ i ∈ Finset.Ico ex (t + 1), (job_suspended_at j i).toNat := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.mem_Ico] at hi
          have hle : i ≤ t := Nat.lt_succ_iff.mp hi.2
          rw [hAllSusp i hi.1 hle]; simp [Bool.toNat]
      _ ≤ ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
            (job_suspended_at j i).toNat :=
          Finset.sum_le_sum_of_subset_of_nonneg hSubset (fun i _ _ => Nat.zero_le _)
  · -- Backward
    intro ⟨hNCOMP, hEXle, hLT⟩
    simp only [suspension_duration, build_suspension_duration] at hLT
    have hZeroBefore : ∀ i, i < ex → i < t_max → S i = S ex → (job_suspended_at j i).toNat = 0 := by
      intro i hi_lt hi_tmax hserv
      cases h_case : job_suspended_at j i with
      | false => simp [Bool.toNat]
      | true =>
        exfalso
        have h_arr_i : has_arrived job_arrival j i := H_arrived j i hi_tmax h_case
        have h_less : S i < S t :=
          less_service_before_start_of_suspension job_arrival sched H_jobs_must_arrive_to_execute j t i
            h_arr_i hi_lt
        have h_same : S ex = S t :=
          same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t
        omega
    have hSumBefore : ∑ i ∈ (Finset.Ico 0 ex).filter (fun t_1 => S t_1 = S ex),
        (job_suspended_at j i).toNat = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi
      exact hZeroBefore i hi.1.2 (Nat.lt_trans (Nat.lt_of_lt_of_le hi.1.2 hEXle) h_lt) hi.2
    have h_split_sum : ∑ i ∈ (Finset.Ico 0 t_max).filter (fun t_1 => S t_1 = S ex),
        (job_suspended_at j i).toNat =
        ∑ i ∈ (Finset.Ico 0 ex).filter (fun t_1 => S t_1 = S ex),
          (job_suspended_at j i).toNat +
        ∑ i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex),
          (job_suspended_at j i).toNat := by
      rw [← Finset.sum_union]
      congr 1
      · rw [← Finset.filter_union]
        congr 1
        exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (Nat.le_of_lt (Nat.lt_of_le_of_lt hEXle h_lt))).symm
      · apply Finset.disjoint_filter_filter
        exact Finset.Ico_disjoint_Ico_consecutive 0 ex t_max
    rw [h_split_sum, hSumBefore, Nat.zero_add] at hLT
    by_contra hNotSusp
    rw [Bool.not_eq_true] at hNotSusp
    have hNoSuspAfter : ∀ i, i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex) →
        t ≤ i → (job_suspended_at j i).toNat = 0 := by
      intro i hi hti
      simp only [Finset.mem_filter, Finset.mem_Ico] at hi
      cases h_case : job_suspended_at j i with
      | false => simp [Bool.toNat]
      | true =>
        exfalso
        rcases Nat.eq_or_lt_of_le hti with rfl | hgt
        · rw [h_case] at hNotSusp; simp at hNotSusp
        · have hSameServEx : S ex = S t :=
            same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t
          have hServ_i_eq_t : S i = S t := by have := hi.2; simp only [hS_def] at this hSameServEx ⊢; linarith
          have hSame_last : time_after_last_execution job_arrival sched j i = ex := by
            have h2 : service sched j (time_after_last_execution job_arrival sched j i) =
                service sched j i :=
              same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j i
            have h3 : service sched j (time_after_last_execution job_arrival sched j t) =
                service sched j t :=
              same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j t
            have h4 : service sched j (time_after_last_execution job_arrival sched j i) =
                service sched j (time_after_last_execution job_arrival sched j t) := by
              rw [h2]; simp only [hS_def] at hServ_i_eq_t hSameServEx; rw [hServ_i_eq_t, ← h3]
            have h5 := same_service_implies_same_last_execution job_arrival sched H_jobs_must_arrive_to_execute j
                (time_after_last_execution job_arrival sched j i)
                (time_after_last_execution job_arrival sched j t) h4
            rw [last_execution_idempotent job_arrival sched H_jobs_must_arrive_to_execute j i,
                last_execution_idempotent job_arrival sched H_jobs_must_arrive_to_execute j t] at h5
            exact h5
          have : job_suspended_at j t = true :=
            H_continuous_suspension j i t hi.1.2 h_case ⟨by rw [hSame_last]; exact hEXle, hgt⟩
          rw [this] at hNotSusp; simp at hNotSusp
    have hSumBound : ∑ i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex),
        (job_suspended_at j i).toNat ≤ t - ex := by
      calc ∑ i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat
          ≤ ∑ i ∈ (Finset.Ico ex t).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat +
            ∑ i ∈ (Finset.Ico t t_max).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat := by
            rw [← Finset.sum_union]
            · apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro x hx
                simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_union] at hx ⊢
                obtain ⟨⟨hge, hlt_tmax⟩, hserv⟩ := hx
                by_cases hxt : x < t
                · left; exact ⟨⟨hge, hxt⟩, hserv⟩
                · right; push_neg at hxt; exact ⟨⟨hxt, hlt_tmax⟩, hserv⟩
              · intro i _ _; exact Nat.zero_le _
            · apply Finset.disjoint_filter_filter
              exact Finset.Ico_disjoint_Ico_consecutive ex t t_max
        _ ≤ ∑ i ∈ (Finset.Ico ex t).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat + 0 := by
            apply Nat.add_le_add_left
            apply Nat.le_of_eq
            apply Finset.sum_eq_zero
            intro i hi
            have hi_mem : i ∈ (Finset.Ico t t_max).filter (fun t_1 => S t_1 = S ex) := hi
            rw [Finset.mem_filter] at hi_mem
            have hi_ico := hi_mem.1
            rw [Finset.mem_Ico] at hi_ico
            apply hNoSuspAfter i
            · simp only [Finset.mem_filter, Finset.mem_Ico]
              exact ⟨⟨Nat.le_trans hEXle hi_ico.1, hi_ico.2⟩, hi_mem.2⟩
            · exact hi_ico.1
        _ ≤ t - ex := by
            rw [Nat.add_zero]
            calc ∑ i ∈ (Finset.Ico ex t).filter (fun t_1 => S t_1 = S ex),
                    (job_suspended_at j i).toNat
                ≤ ∑ i ∈ (Finset.Ico ex t).filter (fun t_1 => S t_1 = S ex), 1 :=
                  Finset.sum_le_sum (fun i _ => by cases job_suspended_at j i <;> simp [Bool.toNat])
              _ ≤ ∑ _i ∈ Finset.Ico ex t, 1 :=
                  Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => Nat.zero_le _)
              _ = t - ex := by rw [Finset.sum_const, smul_eq_mul, mul_one, Nat.card_Ico]
    -- hLT : t < ex + sum_after_ex (with ex unfolded in hLT)
    -- hSumBound : sum_after_ex ≤ t - ex
    -- hEXle : ex ≤ t
    have h_bound : ex + ∑ i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex),
        (job_suspended_at j i).toNat ≤ t := by
      calc ex + ∑ i ∈ (Finset.Ico ex t_max).filter (fun t_1 => S t_1 = S ex),
              (job_suspended_at j i).toNat
          ≤ ex + (t - ex) := Nat.add_le_add_left hSumBound ex
        _ = t := Nat.add_sub_cancel' hEXle
    -- hLT uses time_after_last_execution literally, not ex
    change t < ex + _ at hLT
    exact Nat.not_le.mpr hLT h_bound

end BuildingSuspensionTable

end SuspensionTableConstruction

end

end Prosa.Classic.Model.Schedule.Uni.Susp.Build_suspension_table
