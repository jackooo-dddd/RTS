-- Translated from: ../rt-proofs/classic/model/arrival/basic/arrival_bounds.v
import Prosa.Classic.Util.Div_mod
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

namespace Prosa.Classic.Model.Arrival.Basic.Arrival_bounds

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Util.Div_mod
open Prosa.Classic.Util.Div_mod

section TaskArrivalDefs

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)

def sporadic_task_model (job_arrival : Job → Time) (task_period : Task → Time) :=
  ∀ (j j' : Job),
    j ≠ j' →
    arrives_in arr_seq j →
    arrives_in arr_seq j' →
    job_task j = job_task j' →
    job_arrival j ≤ job_arrival j' →
    job_arrival j' ≥ job_arrival j + task_period (job_task j)

def arrivals_of_task_between (tsk : Task) (t1 t2 : Time) : List Job :=
  (jobs_arrived_between arr_seq t1 t2).filter (fun j => decide (job_task j = tsk))

def num_arrivals_of_task (tsk : Task) (t1 t2 : Time) : Nat :=
  (arrivals_of_task_between job_task arr_seq tsk t1 t2).length

theorem num_arrivals_of_task_cat (tsk : Task)
    (t t1 t2 : Time) (h : t1 ≤ t ∧ t ≤ t2) :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 =
    num_arrivals_of_task job_task arr_seq tsk t1 t +
    num_arrivals_of_task job_task arr_seq tsk t t2 := by
  unfold num_arrivals_of_task arrivals_of_task_between
  rw [job_arrived_between_cat arr_seq t1 t t2 h.1 h.2]
  rw [List.filter_append, List.length_append]

end TaskArrivalDefs

section DistanceBetweenSporadicJobs

variable {Task : Type _} [DecidableEq Task]
variable (task_period : Task → Time)
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)
variable (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
variable (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
variable (H_sporadic_jobs : sporadic_task_model job_task arr_seq job_arrival task_period)
variable (tsk : Task)
variable (t1 t2 : Time)
variable (elem : Job)

private noncomputable def sorted_jobs_dist : List Job :=
  (arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
    (fun j j' => job_arrival j ≤ job_arrival j')

private noncomputable def nth_job_dist (idx : Nat) : Job :=
  (sorted_jobs_dist job_arrival job_task arr_seq tsk t1 t2).getD idx elem

include H_consistent_arrivals in
theorem sorted_arrivals_properties_of_nth
    (idx : Nat)
    (h_idx : idx < num_arrivals_of_task job_task arr_seq tsk t1 t2) :
    t1 ≤ job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem idx) ∧
    job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem idx) < t2 ∧
    job_task (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem idx) = tsk ∧
    arrives_in arr_seq (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem idx) := by
  unfold nth_job_dist sorted_jobs_dist
  set sj := (arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
    (fun j j' => job_arrival j ≤ job_arrival j')
  have h_perm := List.mergeSort_perm
    (arrivals_of_task_between job_task arr_seq tsk t1 t2)
    (fun j j' => job_arrival j ≤ job_arrival j')
  have h_len : sj.length = (arrivals_of_task_between job_task arr_seq tsk t1 t2).length :=
    h_perm.length_eq
  unfold num_arrivals_of_task at h_idx
  rw [← h_len] at h_idx
  have h_getD_eq : sj.getD idx elem = sj[idx] := (List.getElem_eq_getD elem).symm
  have h_mem : sj.getD idx elem ∈ sj := by
    rw [h_getD_eq]; exact List.getElem_mem ..
  have h_mem_orig : sj.getD idx elem ∈ arrivals_of_task_between job_task arr_seq tsk t1 t2 :=
    h_perm.mem_iff.mp h_mem
  unfold arrivals_of_task_between at h_mem_orig
  rw [List.mem_filter] at h_mem_orig
  obtain ⟨h_in_arr, h_task⟩ := h_mem_orig
  simp only [decide_eq_true_eq] at h_task
  have h_arrived := in_arrivals_implies_arrived_between job_arrival arr_seq
    H_consistent_arrivals _ t1 t2 h_in_arr
  have h_arrives := in_arrivals_implies_arrived job_arrival arr_seq
    H_consistent_arrivals _ t1 t2 h_in_arr
  exact ⟨h_arrived.1, h_arrived.2, h_task, h_arrives⟩

include H_consistent_arrivals H_no_duplicate_arrivals in
theorem sorted_arrivals_current_differs_from_next
    (idx : Nat)
    (h_idx : idx < (num_arrivals_of_task job_task arr_seq tsk t1 t2) - 1) :
    nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem idx ≠
    nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem (idx + 1) := by
  unfold nth_job_dist sorted_jobs_dist
  set sj := (arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
    (fun j j' => job_arrival j ≤ job_arrival j')
  have h_perm := List.mergeSort_perm
    (arrivals_of_task_between job_task arr_seq tsk t1 t2)
    (fun j j' => job_arrival j ≤ job_arrival j')
  have h_len : sj.length = (arrivals_of_task_between job_task arr_seq tsk t1 t2).length :=
    h_perm.length_eq
  unfold num_arrivals_of_task at h_idx
  rw [← h_len] at h_idx
  have h_nodup_orig : (arrivals_of_task_between job_task arr_seq tsk t1 t2).Nodup := by
    unfold arrivals_of_task_between
    exact List.Nodup.filter _ (arrivals_uniq job_arrival arr_seq H_consistent_arrivals
      H_no_duplicate_arrivals t1 t2)
  have h_nodup : sj.Nodup := h_perm.nodup_iff.mpr h_nodup_orig
  have h_idx1 : idx < sj.length := by omega
  have h_idx2 : idx + 1 < sj.length := by omega
  intro heq
  have h1 : sj.getD idx elem = sj[idx] := (List.getElem_eq_getD elem).symm
  have h2 : sj.getD (idx + 1) elem = sj[idx + 1] := (List.getElem_eq_getD elem).symm
  rw [h1, h2] at heq
  have : idx = idx + 1 := (List.Nodup.getElem_inj_iff h_nodup).mp heq
  omega

include H_consistent_arrivals H_no_duplicate_arrivals H_sporadic_jobs in
theorem sorted_arrivals_separated_by_period
    (idx : Nat)
    (h_idx : idx < (num_arrivals_of_task job_task arr_seq tsk t1 t2) - 1) :
    job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem (idx + 1)) ≥
    job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem idx) +
      task_period tsk := by
  have h_idx_lt : idx < num_arrivals_of_task job_task arr_seq tsk t1 t2 := by omega
  have h_idx1_lt : idx + 1 < num_arrivals_of_task job_task arr_seq tsk t1 t2 := by omega
  have NTH := sorted_arrivals_properties_of_nth job_arrival job_task arr_seq
    H_consistent_arrivals tsk t1 t2 elem idx h_idx_lt
  have NTH1 := sorted_arrivals_properties_of_nth job_arrival job_task arr_seq
    H_consistent_arrivals tsk t1 t2 elem (idx + 1) h_idx1_lt
  have NEQ := sorted_arrivals_current_differs_from_next job_arrival job_task arr_seq
    H_consistent_arrivals H_no_duplicate_arrivals tsk t1 t2 elem idx h_idx
  have h_le : job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem idx) ≤
      job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem (idx + 1)) := by
    unfold nth_job_dist sorted_jobs_dist
    set sj := (arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
      (fun j j' => decide (job_arrival j ≤ job_arrival j'))
    have h_perm := List.mergeSort_perm
      (arrivals_of_task_between job_task arr_seq tsk t1 t2)
      (fun j j' => decide (job_arrival j ≤ job_arrival j'))
    have h_len : sj.length = (arrivals_of_task_between job_task arr_seq tsk t1 t2).length :=
      h_perm.length_eq
    have h_sj_idx : idx < sj.length := by
      have : sj.length = num_arrivals_of_task job_task arr_seq tsk t1 t2 := by
        show sj.length = (arrivals_of_task_between job_task arr_seq tsk t1 t2).length
        exact h_len
      linarith
    have h_sj_idx1 : idx + 1 < sj.length := by
      have : sj.length = num_arrivals_of_task job_task arr_seq tsk t1 t2 := by
        show sj.length = (arrivals_of_task_between job_task arr_seq tsk t1 t2).length
        exact h_len
      linarith
    have h_trans : ∀ a b c : Job,
        (decide (job_arrival a ≤ job_arrival b) = true) →
        (decide (job_arrival b ≤ job_arrival c) = true) →
        (decide (job_arrival a ≤ job_arrival c) = true) := by
      intro a b c hab hbc
      rw [decide_eq_true_eq] at hab hbc ⊢
      exact Nat.le_trans hab hbc
    have h_total : ∀ a b : Job,
        (decide (job_arrival a ≤ job_arrival b) || decide (job_arrival b ≤ job_arrival a)) = true := by
      intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Nat.le_or_ge (job_arrival a) (job_arrival b)
    have h_sorted : sj.Pairwise (fun a b => decide (job_arrival a ≤ job_arrival b) = true) :=
      List.pairwise_mergeSort h_trans h_total _
    have h1 : sj.getD idx elem = sj[idx] := (List.getElem_eq_getD elem).symm
    have h2 : sj.getD (idx + 1) elem = sj[idx + 1] := (List.getElem_eq_getD elem).symm
    rw [h1, h2]
    have := List.pairwise_iff_getElem.mp h_sorted idx (idx + 1) h_sj_idx h_sj_idx1 (by omega)
    rw [decide_eq_true_eq] at this; exact this
  have h_task_eq : job_task (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem idx) =
      job_task (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem (idx + 1)) := by
    rw [NTH.2.2.1, NTH1.2.2.1]
  have := H_sporadic_jobs _ _ NEQ NTH.2.2.2 NTH1.2.2.2 h_task_eq h_le
  rw [NTH.2.2.1] at this
  exact this

section FirstAndLastJobs

variable (H_at_least_one_job : num_arrivals_of_task job_task arr_seq tsk t1 t2 ≥ 1)

include H_consistent_arrivals H_no_duplicate_arrivals H_sporadic_jobs in
theorem sorted_arrivals_distance_from_first_job
    (idx : Nat)
    (h_idx : idx < num_arrivals_of_task job_task arr_seq tsk t1 t2) :
    job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem idx) ≥
    job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem 0) +
      idx * task_period tsk := by
  induction idx with
  | zero => simp
  | succ n ih =>
    have h_n_lt : n < num_arrivals_of_task job_task arr_seq tsk t1 t2 := by omega
    have h_n_pred : n < (num_arrivals_of_task job_task arr_seq tsk t1 t2) - 1 := by omega
    have h_sep := sorted_arrivals_separated_by_period task_period job_arrival job_task arr_seq
      H_consistent_arrivals H_no_duplicate_arrivals H_sporadic_jobs tsk t1 t2 elem n h_n_pred
    have h_ih := ih h_n_lt
    calc job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem (n + 1))
        ≥ job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem n) + task_period tsk := h_sep
      _ ≥ (job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem 0) + n * task_period tsk) + task_period tsk := Nat.add_le_add_right h_ih _
      _ = job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem 0) + (n + 1) * task_period tsk := by ring

include H_consistent_arrivals H_no_duplicate_arrivals H_sporadic_jobs H_at_least_one_job in
theorem sorted_arrivals_distance_between_first_and_last :
    job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem
      ((num_arrivals_of_task job_task arr_seq tsk t1 t2) - 1)) ≥
    job_arrival (nth_job_dist job_arrival job_task arr_seq tsk t1 t2 elem 0) +
      ((num_arrivals_of_task job_task arr_seq tsk t1 t2) - 1) * task_period tsk := by
  apply sorted_arrivals_distance_from_first_job task_period job_arrival job_task arr_seq
    H_consistent_arrivals H_no_duplicate_arrivals H_sporadic_jobs tsk t1 t2 elem
  omega

end FirstAndLastJobs

end DistanceBetweenSporadicJobs

namespace ArrivalBounds

section Lemmas

variable {Task : Type _} [DecidableEq Task]
variable (task_period : Task → Time)
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_task : Job → Task)
variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)

section BoundOnSporadicArrivals

variable (H_sporadic_tasks :
  sporadic_task_model job_task arr_seq job_arrival task_period)
variable (t1 t2 : Time)
variable (tsk : Task)
variable (H_period_gt_zero : task_period tsk > 0)

section NoJobs

variable (H_no_jobs : num_arrivals_of_task job_task arr_seq tsk t1 t2 = 0)

include H_no_jobs in
theorem sporadic_arrival_bound_no_jobs :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 ≤
    div_ceil (t2 - t1) (task_period tsk) := by
  rw [H_no_jobs]
  exact Nat.zero_le _

end NoJobs

section OneJob

  include H_arrival_times_are_consistent in
  theorem sporadic_arrival_bound_more_than_one_point
      (h : num_arrivals_of_task job_task arr_seq tsk t1 t2 > 0) :
      t1 < t2 := by
    unfold num_arrivals_of_task arrivals_of_task_between at h
    have hne : (List.filter (fun j => decide (job_task j = tsk)) (jobs_arrived_between arr_seq t1 t2)).length > 0 := h
    obtain ⟨j, hj_mem⟩ := List.exists_mem_of_length_pos hne
    rw [List.mem_filter] at hj_mem
    have harr := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j t1 t2 hj_mem.1
    exact Nat.lt_of_le_of_lt harr.1 harr.2

variable (H_one_job : num_arrivals_of_task job_task arr_seq tsk t1 t2 = 1)

  include H_arrival_times_are_consistent H_one_job H_period_gt_zero in
  theorem sporadic_arrival_bound_one_job :
      num_arrivals_of_task job_task arr_seq tsk t1 t2 ≤
      div_ceil (t2 - t1) (task_period tsk) := by
    rw [H_one_job]
    have hlt : t1 < t2 := sporadic_arrival_bound_more_than_one_point job_arrival job_task arr_seq
      H_arrival_times_are_consistent t1 t2 tsk (by rw [H_one_job]; omega)
    have hpos : t2 - t1 > 0 := Nat.sub_pos_of_lt hlt
    exact ceil_neq0 (t2 - t1) (task_period tsk) hpos H_period_gt_zero

end OneJob

section AtLeastTwoJobs

variable (H_at_least_two_jobs : num_arrivals_of_task job_task arr_seq tsk t1 t2 ≥ 2)

section DerivingContradiction

variable (H_many_arrivals :
  div_ceil (t2 - t1) (task_period tsk) <
  num_arrivals_of_task job_task arr_seq tsk t1 t2)

variable (elem : Job)

private noncomputable def sorted_jobs_inner : List Job :=
  (arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
    (fun j j' => job_arrival j ≤ job_arrival j')

private noncomputable def nth_job_inner (idx : Nat) : Job :=
  (sorted_jobs_inner job_arrival job_task arr_seq t1 t2 tsk).getD idx elem

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks in
theorem sporadic_arrival_bound_properties_of_nth
    (idx : Nat)
    (h_idx : idx < num_arrivals_of_task job_task arr_seq tsk t1 t2) :
    t1 ≤ job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem idx) ∧
    job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem idx) < t2 ∧
    job_task (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem idx) = tsk ∧
    arrives_in arr_seq (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem idx) := by
  exact sorted_arrivals_properties_of_nth job_arrival job_task arr_seq
    H_arrival_times_are_consistent tsk t1 t2 elem idx h_idx

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs in
theorem sporadic_arrival_bound_distance_between_first_and_last :
    job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem
      ((num_arrivals_of_task job_task arr_seq tsk t1 t2) - 1)) ≥
    job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem 0) +
    (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) * task_period tsk := by
  apply sorted_arrivals_distance_between_first_and_last task_period job_arrival job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks tsk t1 t2 elem
  omega

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs H_many_arrivals H_period_gt_zero in
theorem sporadic_arrival_bound_last_job_too_far :
    job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem 0) + t2 - t1 ≤
    job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem
      ((num_arrivals_of_task job_task arr_seq tsk t1 t2) - 1)) := by
  set n := num_arrivals_of_task job_task arr_seq tsk t1 t2 with hn_def
  set p := task_period tsk with hp_def
  have DIST := sporadic_arrival_bound_distance_between_first_and_last task_period job_arrival
    job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    t1 t2 tsk H_at_least_two_jobs elem
  have h_n_ge2 : n ≥ 2 := H_at_least_two_jobs
  have h_period_pos : p > 0 := H_period_gt_zero
  have h_ceil_lt : div_ceil (t2 - t1) p < n := H_many_arrivals
  have h_ceil_le : div_ceil (t2 - t1) p ≤ n - 1 := Nat.le_sub_one_of_lt h_ceil_lt
  have h_le_period : t2 - t1 ≤ (n - 1) * p := by
    have h_many_le : div_ceil (t2 - t1) p ≤ n - 1 := h_ceil_le
    unfold div_ceil at h_many_le
    split at h_many_le
    · next h_dvd =>
      obtain ⟨k, hk⟩ := h_dvd
      rw [hk, Nat.mul_div_cancel_left _ h_period_pos] at h_many_le
      calc t2 - t1 = p * k := hk
        _ ≤ p * (n - 1) := Nat.mul_le_mul_left _ h_many_le
        _ = (n - 1) * p := Nat.mul_comm _ _
    · next _ =>
      have hdiv_le : (t2 - t1) / p + 1 ≤ n - 1 := h_many_le
      have hlt_mul := Nat.lt_mul_div_succ (t2 - t1) h_period_pos
      exact Nat.le_of_lt (calc t2 - t1 < p * ((t2 - t1) / p + 1) := hlt_mul
        _ ≤ p * (n - 1) := Nat.mul_le_mul_left _ hdiv_le
        _ = (n - 1) * p := Nat.mul_comm _ _)
  have h0_lt_n : (0 : Nat) < n := by omega
  have NTH0 := sporadic_arrival_bound_properties_of_nth task_period job_arrival job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk elem
    0 h0_lt_n
  have h_t1_le := NTH0.1
  have hgt0 : n > 0 := by omega
  have h_t1_lt_t2 : t1 < t2 := sporadic_arrival_bound_more_than_one_point job_arrival
    job_task arr_seq H_arrival_times_are_consistent t1 t2 tsk hgt0
  set af := job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem 0)
  set al := job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem (n - 1))
  have h_assoc : af + t2 - t1 = af + (t2 - t1) :=
    Nat.add_sub_assoc h_t1_lt_t2.le af
  rw [h_assoc]
  exact Nat.le_trans (Nat.add_le_add_left h_le_period _) DIST

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs H_many_arrivals H_period_gt_zero elem in
theorem sporadic_arrival_bound_last_arrives_too_late :
    job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem
      ((num_arrivals_of_task job_task arr_seq tsk t1 t2) - 1)) ≥ t2 := by
  have TOOFAR : job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem 0) + t2 - t1 ≤
    job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem
      ((num_arrivals_of_task job_task arr_seq tsk t1 t2) - 1)) := by
    exact sporadic_arrival_bound_last_job_too_far task_period job_arrival job_task arr_seq
      H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk
      H_period_gt_zero H_at_least_two_jobs H_many_arrivals elem
  have h0lt : 0 < num_arrivals_of_task job_task arr_seq tsk t1 t2 := by
    have := H_at_least_two_jobs; omega
  have NTH0 := sorted_arrivals_properties_of_nth job_arrival job_task arr_seq
    H_arrival_times_are_consistent tsk t1 t2 elem 0 h0lt
  have h_t1_le := NTH0.1
  -- TOOFAR: af + t2 - t1 ≤ al, NTH0.1: t1 ≤ af, goal: al ≥ t2
  -- al ≥ af + t2 - t1 ≥ t1 + t2 - t1 = t2 (since t1 ≤ af)
  -- But in Nat: af + t2 - t1 ≥ t2 when t1 ≤ af
  -- And TOOFAR: al ≥ af + t2 - t1
  -- So al ≥ af + t2 - t1 ≥ t2 (when t1 ≤ af, af + t2 - t1 = af + t2 - t1 ≥ 0 + t2 = t2)
  -- Actually: af + t2 - t1 = af - t1 + t2 when t1 ≤ af. af - t1 ≥ 0, so af - t1 + t2 ≥ t2.
  -- So al ≥ af + t2 - t1 ≥ t2.
  -- TOOFAR: a₀ + t2 - t1 ≤ aₙ, h_t1_le: t1 ≤ a₀, goal: aₙ ≥ t2
  -- Since h_t1_le: t1 ≤ a₀, and a₀ + t2 - t1 = a₀ + t2 - t1:
  -- a₀ + t2 - t1 = a₀ - t1 + t2 (since t1 ≤ a₀) ≥ 0 + t2 = t2
  -- So aₙ ≥ a₀ + t2 - t1 ≥ t2
  set a0 := job_arrival (nth_job_inner job_arrival job_task arr_seq t1 t2 tsk elem 0)
  have h_t1_le_a0 : t1 ≤ a0 := h_t1_le
  have hge : t2 ≤ a0 + t2 - t1 :=
    Nat.le_sub_of_add_le (show t2 + t1 ≤ a0 + t2 from
      calc t2 + t1 = t1 + t2 := Nat.add_comm t2 t1
        _ ≤ a0 + t2 := Nat.add_le_add_right h_t1_le_a0 t2)
  exact Nat.le_trans hge TOOFAR

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs H_many_arrivals H_period_gt_zero elem in
theorem sporadic_arrival_bound_case_3_contradiction : False := by
  have LATE := sporadic_arrival_bound_last_arrives_too_late task_period job_arrival job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk
    H_period_gt_zero H_at_least_two_jobs H_many_arrivals elem
  have hnm1lt : num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1 <
    num_arrivals_of_task job_task arr_seq tsk t1 t2 := by
    have := H_at_least_two_jobs; omega
  have NTH := sorted_arrivals_properties_of_nth job_arrival job_task arr_seq
    H_arrival_times_are_consistent tsk t1 t2 elem
    (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) hnm1lt
  have hlt := NTH.2.1
  exact absurd LATE (not_le.mpr hlt)

end DerivingContradiction

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_at_least_two_jobs H_period_gt_zero in
theorem sporadic_task_arrival_bound_at_least_two_jobs :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 ≤
    div_ceil (t2 - t1) (task_period tsk) := by
  by_contra h
  push_neg at h
  have hlen_pos : 0 < (arrivals_of_task_between job_task arr_seq tsk t1 t2).length := by
    change 0 < num_arrivals_of_task job_task arr_seq tsk t1 t2; omega
  obtain ⟨j, _⟩ := List.exists_mem_of_length_pos hlen_pos
  exact @sporadic_arrival_bound_case_3_contradiction _ _ task_period _ _ job_arrival job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    t1 t2 tsk H_period_gt_zero H_at_least_two_jobs h j

end AtLeastTwoJobs

include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    H_period_gt_zero in
theorem sporadic_task_arrival_bound :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 ≤
    div_ceil (t2 - t1) (task_period tsk) := by
  by_cases h0 : num_arrivals_of_task job_task arr_seq tsk t1 t2 = 0
  · rw [h0]; exact Nat.zero_le _
  · by_cases h1 : num_arrivals_of_task job_task arr_seq tsk t1 t2 = 1
    · rw [h1]
      have hlt : t1 < t2 := sporadic_arrival_bound_more_than_one_point job_arrival job_task arr_seq
        H_arrival_times_are_consistent t1 t2 tsk (by rw [h1]; omega)
      have hpos : t2 - t1 > 0 := Nat.sub_pos_of_lt hlt
      exact ceil_neq0 (t2 - t1) (task_period tsk) hpos H_period_gt_zero
    · have h_ge2 : num_arrivals_of_task job_task arr_seq tsk t1 t2 ≥ 2 := by omega
      exact sporadic_task_arrival_bound_at_least_two_jobs task_period job_arrival job_task arr_seq
        H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk
        H_period_gt_zero h_ge2

end BoundOnSporadicArrivals

end Lemmas

end ArrivalBounds

end Prosa.Classic.Model.Arrival.Basic.Arrival_bounds
