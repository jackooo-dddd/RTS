-- Translated from: ../rt-proofs/classic/model/schedule/uni/susp/last_execution.v
import Prosa.Classic.Util.Sum
import Prosa.Classic.Util.Step_function
import Prosa.Classic.Util.Minmax
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Util.Minmax

section TimeAfterLastExecution

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (sched : schedule Job)

section Defs

variable (j : Job)
variable (t : Time)

noncomputable def scheduled_before : Bool :=
  decide (∃ t0 : Fin t, scheduled_at sched j t0.val = true)

noncomputable def last_time_scheduled : Nat :=
  match max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t with
  | some m => m
  | none => 0

noncomputable def time_after_last_execution : Time :=
  if scheduled_before sched j t then
    last_time_scheduled sched j t + 1
  else job_arrival j

end Defs

section Lemmas

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
include H_jobs_must_arrive_to_execute

variable (j : Job)

section JobHasArrived

theorem last_execution_after_arrival :
    ∀ t, has_arrived job_arrival j (time_after_last_execution job_arrival sched j t) := by
  intro t
  simp only [time_after_last_execution]
  split
  · rename_i h_sb
    simp only [scheduled_before, decide_eq_true_eq] at h_sb
    obtain ⟨⟨t0, ht0⟩, hsched⟩ := h_sb
    simp only [last_time_scheduled]
    have hne : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t ≠ none :=
      max_nat_cond_exists _ _ _ t0 ⟨Nat.zero_le _, ht0⟩ hsched
    obtain ⟨m, hm⟩ : ∃ m, max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t = some m := by
      cases h : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t with
      | some m => exact ⟨m, rfl⟩
      | none => exact absurd h (by simp [hne])
    rw [hm]
    have hinfo := max_nat_cond_in_seq _ _ _ _ hm
    have harr : job_arrival j ≤ m := H_jobs_must_arrive_to_execute j m hinfo.2.2
    exact Nat.le_succ_of_le harr
  · exact Nat.le_refl _

end JobHasArrived

section Monotonicity

variable (t1 : Time)
variable (H_after_arrival : has_arrived job_arrival j t1)
include H_after_arrival

theorem last_execution_monotonic :
    ∀ t2, t1 ≤ t2 →
      time_after_last_execution job_arrival sched j t1 ≤
      time_after_last_execution job_arrival sched j t2 := by
  intro t2 hle
  simp only [time_after_last_execution]
  by_cases h1 : scheduled_before sched j t1 = true
  · simp only [h1, ↓reduceIte]
    simp only [scheduled_before, decide_eq_true_eq] at h1
    obtain ⟨⟨t0, ht0⟩, hsched0⟩ := h1
    have h2 : scheduled_before sched j t2 = true := by
      simp only [scheduled_before, decide_eq_true_eq]
      exact ⟨⟨t0, Nat.lt_of_lt_of_le ht0 hle⟩, hsched0⟩
    simp only [h2, ↓reduceIte, last_time_scheduled]
    have hne1 : max_nat_cond (fun x => scheduled_at sched j x) 0 t1 ≠ none :=
      max_nat_cond_exists _ _ _ t0 ⟨Nat.zero_le _, ht0⟩ hsched0
    obtain ⟨m1, hm1⟩ : ∃ m, max_nat_cond (fun x => scheduled_at sched j x) 0 t1 = some m := by
      cases h : max_nat_cond (fun x => scheduled_at sched j x) 0 t1 with
      | some m => exact ⟨m, rfl⟩ | none => exact absurd h (by simp [hne1])
    have hne2 : max_nat_cond (fun x => scheduled_at sched j x) 0 t2 ≠ none :=
      max_nat_cond_exists _ _ _ t0 ⟨Nat.zero_le _, Nat.lt_of_lt_of_le ht0 hle⟩ hsched0
    obtain ⟨m2, hm2⟩ : ∃ m, max_nat_cond (fun x => scheduled_at sched j x) 0 t2 = some m := by
      cases h : max_nat_cond (fun x => scheduled_at sched j x) 0 t2 with
      | some m => exact ⟨m, rfl⟩ | none => exact absurd h (by simp [hne2])
    rw [hm1, hm2]
    have hinfo1 := max_nat_cond_in_seq _ _ _ _ hm1
    have hm1_lt : m1 < t1 := hinfo1.2.1
    have hm1_sched : scheduled_at sched j m1 = true := hinfo1.2.2
    have hm1_lt_t2 : m1 < t2 := Nat.lt_of_lt_of_le hm1_lt hle
    have hle_m : m1 ≤ m2 :=
      max_nat_cond_computes_max _ _ _ _ hm2 m1 ⟨Nat.zero_le _, hm1_lt_t2⟩ hm1_sched
    exact Nat.succ_le_succ hle_m
  · simp only [Bool.not_eq_true] at h1; simp only [h1, ↓reduceIte]
    by_cases h2 : scheduled_before sched j t2 = true
    · simp only [h2, ↓reduceIte]
      simp only [scheduled_before, decide_eq_true_eq] at h2
      obtain ⟨⟨t0', ht0'⟩, hsched0'⟩ := h2
      simp only [last_time_scheduled]
      have hne2 : max_nat_cond (fun x => scheduled_at sched j x) 0 t2 ≠ none :=
        max_nat_cond_exists _ _ _ t0' ⟨Nat.zero_le _, ht0'⟩ hsched0'
      obtain ⟨m2, hm2⟩ : ∃ m, max_nat_cond (fun x => scheduled_at sched j x) 0 t2 = some m := by
        cases h : max_nat_cond (fun x => scheduled_at sched j x) 0 t2 with
        | some m => exact ⟨m, rfl⟩ | none => exact absurd h (by simp [hne2])
      rw [hm2]
      have hinfo2 := max_nat_cond_in_seq _ _ _ _ hm2
      have hm2_sched : scheduled_at sched j m2 = true := hinfo2.2.2
      have harr : job_arrival j ≤ m2 := H_jobs_must_arrive_to_execute j m2 hm2_sched
      exact Nat.le_succ_of_le harr
    · simp only [Bool.not_eq_true] at h2
      simp only [h2, Bool.false_eq_true, ↓reduceIte]
      exact le_refl _

end Monotonicity

section Idempotence

theorem last_execution_idempotent :
    ∀ t,
      time_after_last_execution job_arrival sched j
        (time_after_last_execution job_arrival sched j t) =
      time_after_last_execution job_arrival sched j t := by
  intro t
  set tle := time_after_last_execution job_arrival sched j t
  simp only [time_after_last_execution] at tle ⊢
  by_cases h_ex : scheduled_before sched j t = true
  · simp only [scheduled_before, decide_eq_true_eq] at h_ex
    obtain ⟨⟨t0, ht0⟩, hsched0⟩ := h_ex
    have hne : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t ≠ none :=
      max_nat_cond_exists _ _ _ t0 ⟨Nat.zero_le _, ht0⟩ hsched0
    obtain ⟨m, hm⟩ : ∃ m, max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t = some m := by
      cases h : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t with
      | some m => exact ⟨m, rfl⟩ | none => exact absurd h (by simp [hne])
    have hinfo := max_nat_cond_in_seq _ _ _ _ hm
    have hm_sched : scheduled_at sched j m = true := hinfo.2.2
    have htle : tle = m + 1 := by
      simp only [tle, time_after_last_execution, scheduled_before]
      have : decide (∃ t0 : Fin t, scheduled_at sched j t0.val = true) = true := by
        simp only [decide_eq_true_eq]; exact ⟨⟨t0, ht0⟩, hsched0⟩
      simp only [this, ↓reduceIte, last_time_scheduled, hm]
    have h_sb_tle : scheduled_before sched j (m + 1) = true := by
      simp only [scheduled_before, decide_eq_true_eq]
      exact ⟨⟨m, Nat.lt_succ_iff.mpr (le_refl _)⟩, hm_sched⟩
    simp only [htle, h_sb_tle, ↓reduceIte, last_time_scheduled]
    have hne' : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 (m + 1) ≠ none :=
      max_nat_cond_exists _ _ _ m ⟨Nat.zero_le _, Nat.lt_succ_iff.mpr (le_refl _)⟩ hm_sched
    obtain ⟨m', hm'⟩ : ∃ m', max_nat_cond (fun t0 => scheduled_at sched j t0) 0 (m + 1) = some m' := by
      cases h : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 (m + 1) with
      | some m' => exact ⟨m', rfl⟩ | none => exact absurd h (by simp [hne'])
    rw [hm']
    have hinfo' := max_nat_cond_in_seq _ _ _ _ hm'
    have hm'_lt : m' < m + 1 := hinfo'.2.1
    have hm'_le_m : m' ≤ m := Nat.lt_succ_iff.mp hm'_lt
    have hm_le_m' : m ≤ m' :=
      max_nat_cond_computes_max _ _ _ _ hm' m ⟨Nat.zero_le _, Nat.lt_succ_iff.mpr (le_refl _)⟩ hm_sched
    have : m' = m := le_antisymm hm'_le_m hm_le_m'
    subst this; simp
  · simp only [Bool.not_eq_true] at h_ex
    have htle : tle = job_arrival j := by
      simp only [tle, time_after_last_execution, scheduled_before] at h_ex ⊢
      simp only [h_ex, Bool.false_eq_true, ↓reduceIte]
    have h_sb_arr : scheduled_before sched j (job_arrival j) = false := by
      simp only [scheduled_before, decide_eq_false_iff_not, not_exists]
      intro ⟨t', ht'⟩ hsched'
      have harr : job_arrival j ≤ t' := H_jobs_must_arrive_to_execute j t' hsched'
      exact absurd (Nat.lt_of_lt_of_le ht' (le_refl _)) (not_lt.mpr harr)
    simp only [htle, h_sb_arr, Bool.false_eq_true, ↓reduceIte]

end Idempotence

section BoundedByIdentity

variable (t : Time)
variable (H_after_arrival : has_arrived job_arrival j t)
include H_after_arrival

theorem last_execution_bounded_by_identity :
    time_after_last_execution job_arrival sched j t ≤ t := by
  simp only [time_after_last_execution]
  split
  · rename_i h_sb
    simp only [scheduled_before, decide_eq_true_eq] at h_sb
    obtain ⟨⟨t0, ht0⟩, hsched⟩ := h_sb
    simp only [last_time_scheduled]
    have hne : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t ≠ none :=
      max_nat_cond_exists _ _ _ t0 ⟨Nat.zero_le _, ht0⟩ hsched
    obtain ⟨m, hm⟩ : ∃ m, max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t = some m := by
      cases h : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t with
      | some m => exact ⟨m, rfl⟩ | none => exact absurd h (by simp [hne])
    rw [hm]
    have hinfo := max_nat_cond_in_seq _ _ _ _ hm
    exact Nat.succ_le_of_lt hinfo.2.1
  · exact H_after_arrival

end BoundedByIdentity

section SameLastExecution

variable (t t' : Time)
variable (H_same_service : service sched j t = service sched j t')
include H_same_service

theorem same_service_implies_same_last_execution :
    time_after_last_execution job_arrival sched j t =
    time_after_last_execution job_arrival sched j t' := by
  open Prosa.Classic.Util.Sum in
  have IFF := same_service_implies_scheduled_at_earlier_times sched j t t' H_same_service
  have h_sb_eq : scheduled_before sched j t = scheduled_before sched j t' := by
    simp only [scheduled_before]; congr 1; exact propext IFF
  simp only [time_after_last_execution, h_sb_eq]
  split
  · rename_i h_sb
    simp only [scheduled_before, decide_eq_true_eq] at h_sb
    simp only [last_time_scheduled]
    have h_sb_t : (scheduled_before sched j t) = true := by rw [h_sb_eq]; simp [scheduled_before, decide_eq_true_eq]; exact h_sb
    simp only [scheduled_before, decide_eq_true_eq] at h_sb_t
    obtain ⟨⟨t0, ht0⟩, hsched0⟩ := h_sb_t
    obtain ⟨⟨t0', ht0'⟩, hsched0'⟩ := h_sb
    have hne_t : max_nat_cond (fun x => scheduled_at sched j x) 0 t ≠ none :=
      max_nat_cond_exists _ _ _ t0 ⟨Nat.zero_le _, ht0⟩ hsched0
    obtain ⟨mt, hmt⟩ : ∃ m, max_nat_cond (fun x => scheduled_at sched j x) 0 t = some m := by
      cases h : max_nat_cond (fun x => scheduled_at sched j x) 0 t with
      | some m => exact ⟨m, rfl⟩ | none => exact absurd h (by simp [hne_t])
    have hne_t' : max_nat_cond (fun x => scheduled_at sched j x) 0 t' ≠ none :=
      max_nat_cond_exists _ _ _ t0' ⟨Nat.zero_le _, ht0'⟩ hsched0'
    obtain ⟨mt', hmt'⟩ : ∃ m, max_nat_cond (fun x => scheduled_at sched j x) 0 t' = some m := by
      cases h : max_nat_cond (fun x => scheduled_at sched j x) 0 t' with
      | some m => exact ⟨m, rfl⟩ | none => exact absurd h (by simp [hne_t'])
    rw [hmt, hmt']; simp only
    have hmt_info := max_nat_cond_in_seq _ _ _ _ hmt
    have hmt'_info := max_nat_cond_in_seq _ _ _ _ hmt'
    have hmt_lt : mt < t := hmt_info.2.1
    have hmt_sched : scheduled_at sched j mt = true := hmt_info.2.2
    have hmt'_lt : mt' < t' := hmt'_info.2.1
    have hmt'_sched : scheduled_at sched j mt' = true := hmt'_info.2.2
    congr 1; apply le_antisymm
    · by_cases h1 : mt < t'
      · exact max_nat_cond_computes_max _ _ _ _ hmt' mt ⟨Nat.zero_le _, h1⟩ hmt_sched
      · push_neg at h1; exfalso
        have h_split : ∑ x ∈ Finset.Ico 0 t, service_at sched j x =
          ∑ x ∈ Finset.Ico 0 t', service_at sched j x + ∑ x ∈ Finset.Ico t' t, service_at sched j x := by
          rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 t' t)]; congr 1
          exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (le_of_lt (Nat.lt_of_le_of_lt h1 hmt_lt))).symm
        have hmt_mem : mt ∈ Finset.Ico t' t := Finset.mem_Ico.mpr ⟨h1, hmt_lt⟩
        have hmt_sa : service_at sched j mt ≥ 1 := by
          simp only [service_at, scheduled_at] at hmt_sched ⊢; simp [hmt_sched, Bool.toNat]
        have : service sched j t' < service sched j t := by
          simp only [service, service_during]; rw [h_split]
          linarith [Finset.single_le_sum (f := fun x => service_at sched j x) (fun i _ => Nat.zero_le _) hmt_mem]
        linarith [H_same_service]
    · by_cases h1 : mt' < t
      · exact max_nat_cond_computes_max _ _ _ _ hmt mt' ⟨Nat.zero_le _, h1⟩ hmt'_sched
      · push_neg at h1; exfalso
        have h_split : ∑ x ∈ Finset.Ico 0 t', service_at sched j x =
          ∑ x ∈ Finset.Ico 0 t, service_at sched j x + ∑ x ∈ Finset.Ico t t', service_at sched j x := by
          rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 t t')]; congr 1
          exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (le_of_lt (Nat.lt_of_le_of_lt h1 hmt'_lt))).symm
        have hmt'_mem : mt' ∈ Finset.Ico t t' := Finset.mem_Ico.mpr ⟨h1, hmt'_lt⟩
        have hmt'_sa : service_at sched j mt' ≥ 1 := by
          simp only [service_at, scheduled_at] at hmt'_sched ⊢; simp [hmt'_sched, Bool.toNat]
        have : service sched j t < service sched j t' := by
          simp only [service, service_during]; rw [h_split]
          linarith [Finset.single_le_sum (f := fun x => service_at sched j x) (fun i _ => Nat.zero_le _) hmt'_mem]
        linarith [H_same_service]
  · rfl

end SameLastExecution

section SameService

theorem same_service_since_last_execution :
    ∀ t,
      service sched j (time_after_last_execution job_arrival sched j t) =
      service sched j t := by
  open Prosa.Classic.Util.Sum in
  intro t
  simp only [time_after_last_execution]
  by_cases h_ex : scheduled_before sched j t = true
  · simp only [h_ex, ↓reduceIte]
    simp only [scheduled_before, decide_eq_true_eq] at h_ex
    obtain ⟨⟨t0, ht0⟩, hsched0⟩ := h_ex
    simp only [last_time_scheduled]
    have hne : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t ≠ none :=
      max_nat_cond_exists _ _ _ t0 ⟨Nat.zero_le _, ht0⟩ hsched0
    obtain ⟨m, hm⟩ : ∃ m, max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t = some m := by
      cases h : max_nat_cond (fun t0 => scheduled_at sched j t0) 0 t with
      | some m => exact ⟨m, rfl⟩ | none => exact absurd h (by simp [hne])
    rw [hm]
    have hinfo := max_nat_cond_in_seq _ _ _ _ hm
    have hm_lt : m < t := hinfo.2.1
    have hm_sched : scheduled_at sched j m = true := hinfo.2.2
    by_cases h_eq : m + 1 = t
    · rw [h_eq]
    · have hm_succ_lt : m + 1 < t := by omega
      simp only [service, service_during]
      have h_split : ∑ x ∈ Finset.Ico 0 t, service_at sched j x =
        ∑ x ∈ Finset.Ico 0 (m + 1), service_at sched j x + ∑ x ∈ Finset.Ico (m + 1) t, service_at sched j x := by
        rw [← Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 (m + 1) t)]; congr 1
        exact (Finset.Ico_union_Ico_eq_Ico (Nat.zero_le _) (le_of_lt hm_succ_lt)).symm
      have h_zero_tail : ∑ x ∈ Finset.Ico (m + 1) t, service_at sched j x = 0 := by
        apply Finset.sum_eq_zero
        intro i hi; rw [Finset.mem_Ico] at hi
        simp only [service_at]
        have h_not_sched : ¬ (scheduled_at sched j i = true) := by
          intro h_sched_i
          have h_i_le_m : i ≤ m :=
            max_nat_cond_computes_max _ _ _ _ hm i ⟨Nat.zero_le _, hi.2⟩ h_sched_i
          omega
        simp only [scheduled_at] at h_not_sched ⊢
        cases hd : (sched i == some j) <;> simp [Bool.toNat]
        exfalso; apply h_not_sched; simp [scheduled_at, hd]
      rw [h_split, h_zero_tail, add_zero]
  · simp only [Bool.not_eq_true] at h_ex
    simp only [h_ex, Bool.false_eq_true, ↓reduceIte]
    simp only [service, service_during]
    have h_all_zero : ∀ i, i ∈ Finset.Ico 0 t → service_at sched j i = 0 := by
      intro i hi; rw [Finset.mem_Ico] at hi
      simp only [scheduled_before, decide_eq_false_iff_not, not_exists] at h_ex
      have : ¬ (scheduled_at sched j i = true) := h_ex ⟨i, hi.2⟩
      simp only [service_at, scheduled_at] at this ⊢
      cases hd : (sched i == some j) <;> simp [Bool.toNat]
      exfalso; exact this (by simp [scheduled_at, hd])
    rw [Finset.sum_eq_zero h_all_zero]
    have : ∑ t_1 ∈ Finset.Ico 0 (job_arrival j), service_at sched j t_1 = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        rw [Finset.mem_Ico] at hi
        exact service_before_job_arrival_zero job_arrival sched H_jobs_must_arrive_to_execute j i hi.2)
    linarith

end SameService

section ExistsIntermediateExecution

variable (t : Time)
variable (H_j_has_completed : completed_by job_cost sched j t)
variable (s : Time)
variable (H_less_than_cost : s < job_cost j)
include H_j_has_completed H_less_than_cost

theorem exists_last_execution_with_smaller_service :
    ∃ t0,
      service sched j (time_after_last_execution job_arrival sched j t0) = s := by
  have SAME := same_service_since_last_execution job_arrival sched H_jobs_must_arrive_to_execute j
  have h_s_lt : s < service sched j t := by
    unfold completed_by at H_j_has_completed
    exact lt_of_lt_of_le H_less_than_cost H_j_has_completed
  have ⟨x_mid, _, hserv⟩ := exists_intermediate_service sched j t s h_s_lt
  exact ⟨x_mid, by rw [SAME, hserv]⟩

end ExistsIntermediateExecution

section LessServiceBeforeLastExecution

variable (t : Time)
variable (t0 : Time)
variable (H_no_earlier_than_arrival : has_arrived job_arrival j t0)
variable (H_before_last_execution :
  t0 < time_after_last_execution job_arrival sched j t)
include H_no_earlier_than_arrival H_before_last_execution

theorem less_service_before_start_of_suspension :
    service sched j t0 < service sched j t := by
  by_cases h_sb : scheduled_before sched j t = true
  · simp only [scheduled_before, decide_eq_true_eq] at h_sb
    obtain ⟨⟨t0', ht0'⟩, hsched0'⟩ := h_sb
    have h_sb_true : scheduled_before sched j t = true := by
      simp only [scheduled_before, decide_eq_true_eq]; exact ⟨⟨t0', ht0'⟩, hsched0'⟩
    have hne := max_nat_cond_exists (fun x => scheduled_at sched j x) 0 t t0' ⟨Nat.zero_le _, ht0'⟩ hsched0'
    obtain ⟨m, hm⟩ : ∃ m, max_nat_cond (fun x => scheduled_at sched j x) 0 t = some m := by
      cases h : max_nat_cond (fun x => scheduled_at sched j x) 0 t with
      | some m => exact ⟨m, rfl⟩ | none => exact absurd h hne
    have hinfo := max_nat_cond_in_seq _ _ _ _ hm
    have hm_lt_t := hinfo.2.1
    have hm_sched := hinfo.2.2
    have h_lts : last_time_scheduled sched j t = m := by simp only [last_time_scheduled, hm]
    have h_tae_val : time_after_last_execution job_arrival sched j t = m + 1 := by
      simp only [time_after_last_execution, h_sb_true, ↓reduceIte, h_lts]
    rw [h_tae_val] at H_before_last_execution
    have ht0_le_m : t0 ≤ m := Nat.lt_succ_iff.mp H_before_last_execution
    simp only [service, service_during]
    calc ∑ i ∈ Finset.Ico 0 t0, service_at sched j i
        ≤ ∑ i ∈ Finset.Ico 0 m, service_at sched j i := by
          apply Finset.sum_le_sum_of_subset; intro x hx; rw [Finset.mem_Ico] at hx ⊢
          exact ⟨hx.1, Nat.lt_of_lt_of_le hx.2 ht0_le_m⟩
      _ < ∑ i ∈ Finset.Ico 0 t, service_at sched j i := by
          rw [← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le m) (Nat.le_of_lt hm_lt_t)]
          rw [Finset.sum_union (Finset.Ico_disjoint_Ico_consecutive 0 m t)]
          have hm_mem : m ∈ Finset.Ico m t := Finset.mem_Ico.mpr ⟨le_refl _, hm_lt_t⟩
          have hm_sa : service_at sched j m ≥ 1 := by
            simp only [service_at, scheduled_at] at hm_sched ⊢; simp [hm_sched, Bool.toNat]
          linarith [Finset.single_le_sum (f := fun x => service_at sched j x)
            (fun i _ => Nat.zero_le _) hm_mem]
  · simp only [Bool.not_eq_true] at h_sb
    have h_tae_val : time_after_last_execution job_arrival sched j t = job_arrival j := by
      simp only [time_after_last_execution, h_sb, Bool.false_eq_true, ↓reduceIte]
    rw [h_tae_val] at H_before_last_execution
    unfold has_arrived at H_no_earlier_than_arrival
    exact absurd (lt_of_lt_of_le H_before_last_execution H_no_earlier_than_arrival) (lt_irrefl _)

end LessServiceBeforeLastExecution

end Lemmas

end TimeAfterLastExecution

end Prosa.Classic.Model.Schedule.Uni.Susp.Last_execution
