-- Translated from: ../rt-proofs/classic/model/arrival/jitter/task_arrival.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
import Mathlib.Data.List.Sort

namespace Prosa.Classic.Model.Arrival.Jitter.Task_arrival

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence

section NumberOfArrivals

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_jitter : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)

variable (tsk : Task)

def is_job_of_tsk (j : Job) : Bool := is_job_of_task job_task tsk j

noncomputable def actual_arrivals_of_task_between (t1 t2 : Time) :=
  (actual_arrivals_between job_arrival job_jitter arr_seq t1 t2).filter (is_job_of_tsk job_task tsk)

noncomputable def num_actual_arrivals_of_task (t1 t2 : Time) :=
  (actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).length

end NumberOfArrivals

section DistanceBetweenSporadicJobs

variable {Task : Type _} [DecidableEq Task]
variable (task_period : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_jitter : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)

variable (tsk : Task)

variable (t1 t2 : Time)

variable (elem : Job)

private noncomputable def sorted_jobs :=
  (actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
    (fun j j' => decide (job_arrival j ≤ job_arrival j'))

private noncomputable def nth_job (i : ℕ) :=
  (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).getD i elem

theorem sorted_arrivals_properties_of_nth (idx : ℕ)
    (h : idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2) :
    arrival_times_are_consistent job_arrival arr_seq →
    t1 ≤ actual_arrival job_arrival job_jitter (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) ∧
    actual_arrival job_arrival job_jitter (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) < t2 ∧
    job_task (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) = tsk ∧
    arrives_in arr_seq (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) := by
  intro CONS
  set nj := nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx
  have h_len : idx < (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).length := by
    simp only [sorted_jobs, List.length_mergeSort]
    exact h
  have h_in_sorted : nj ∈ sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2 := by
    simp only [nj, nth_job, List.getD]
    rw [List.getElem?_eq_getElem h_len]
    exact List.getElem_mem h_len
  have h_in_orig : nj ∈ actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2 := by
    exact (List.mergeSort_perm _ _).mem_iff.mp h_in_sorted
  simp only [actual_arrivals_of_task_between] at h_in_orig
  rw [List.mem_filter] at h_in_orig
  obtain ⟨h_mem, h_task_bool⟩ := h_in_orig
  have h_task_eq : job_task nj = tsk := by
    simp only [is_job_of_tsk, is_job_of_task] at h_task_bool
    rwa [decide_eq_true_eq] at h_task_bool
  have h_arrived : arrives_in arr_seq nj :=
    in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq CONS nj t1 t2 h_mem
  have h_between : actual_arrival_between job_arrival job_jitter nj t1 t2 :=
    in_actual_arrivals_implies_arrived_between job_arrival job_jitter arr_seq CONS nj t1 t2 h_mem
  exact ⟨h_between.1, h_between.2, h_task_eq, h_arrived⟩

theorem sorted_arrivals_current_differs_from_next (idx : ℕ)
    (h : idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) :
    arrival_times_are_consistent job_arrival arr_seq →
    arrival_sequence_is_a_set arr_seq →
    nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx ≠
    nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem (idx + 1) := by
  intro CONS SET
  have h_len_eq : (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).length =
      num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 := by
    simp only [sorted_jobs, List.length_mergeSort]; rfl
  have h_nodup_orig : (actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).Nodup := by
    simp only [actual_arrivals_of_task_between]
    exact List.Nodup.filter _ (actual_arrivals_uniq job_arrival job_jitter arr_seq CONS SET t1 t2)
  have h_nodup : (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr h_nodup_orig
  have h_idx_lt : idx < (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).length := by omega
  have h_idx1_lt : idx + 1 < (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).length := by omega
  intro heq
  simp only [nth_job] at heq
  have h1 : (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).getD idx elem =
      (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2)[idx] :=
    (List.getElem_eq_getD elem).symm
  have h2 : (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).getD (idx + 1) elem =
      (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2)[idx + 1] :=
    (List.getElem_eq_getD elem).symm
  rw [h1, h2] at heq
  exact absurd ((List.Nodup.getElem_inj_iff h_nodup).mp heq) (by omega)

theorem sorted_arrivals_separated_by_period (idx : ℕ)
    (h : idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) :
    arrival_times_are_consistent job_arrival arr_seq →
    arrival_sequence_is_a_set arr_seq →
    sporadic_task_model task_period job_arrival job_task arr_seq →
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem (idx + 1)) ≥
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) +
    task_period tsk := by
  intro CONS SET SPO
  have h_idx_lt : idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 := by omega
  have h_idx1_lt : idx + 1 < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 := by omega
  have NTH := sorted_arrivals_properties_of_nth job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx h_idx_lt CONS
  have NTH1 := sorted_arrivals_properties_of_nth job_arrival job_jitter job_task arr_seq tsk t1 t2 elem (idx + 1) h_idx1_lt CONS
  have NEQ := sorted_arrivals_current_differs_from_next job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx h CONS SET
  have h_le : job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) ≤
      job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem (idx + 1)) := by
    have h_perm : (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).Perm
        (actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2) :=
      List.mergeSort_perm _ _
    have h_len_eq : (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).length =
        (actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).length :=
      h_perm.length_eq
    have h_sj_idx : idx < (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).length := by
      simp only [num_actual_arrivals_of_task] at h_idx_lt; rw [h_len_eq]; exact h_idx_lt
    have h_sj_idx1 : idx + 1 < (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).length := by
      simp only [num_actual_arrivals_of_task] at h_idx1_lt; rw [h_len_eq]; exact h_idx1_lt
    have h_trans : ∀ a b c : Job,
        (decide (job_arrival a ≤ job_arrival b) = true) →
        (decide (job_arrival b ≤ job_arrival c) = true) →
        (decide (job_arrival a ≤ job_arrival c) = true) := by
      intro a b c hab hbc
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact Nat.le_trans hab hbc
    have h_total : ∀ a b : Job,
        (decide (job_arrival a ≤ job_arrival b) || decide (job_arrival b ≤ job_arrival a)) = true := by
      intro a b
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact Nat.le_or_le (job_arrival a) (job_arrival b)
    have h_sorted : (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).Pairwise
        (fun a b => decide (job_arrival a ≤ job_arrival b) = true) :=
      List.pairwise_mergeSort h_trans h_total _
    simp only [nth_job]
    have h1 : (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).getD idx elem =
        (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2)[idx] :=
      (List.getElem_eq_getD elem).symm
    have h2 : (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2).getD (idx + 1) elem =
        (sorted_jobs job_arrival job_jitter job_task arr_seq tsk t1 t2)[idx + 1] :=
      (List.getElem_eq_getD elem).symm
    rw [h1, h2]
    have := List.pairwise_iff_getElem.mp h_sorted idx (idx + 1) h_sj_idx h_sj_idx1 (by omega)
    rw [decide_eq_true_eq] at this; exact this
  have h_task_eq : job_task (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) =
      job_task (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem (idx + 1)) := by
    rw [NTH.2.2.1, NTH1.2.2.1]
  have := SPO _ _ NEQ NTH.2.2.2 NTH1.2.2.2 h_task_eq h_le
  rw [NTH.2.2.1] at this
  exact this

section FirstAndLastJobs

theorem sorted_arrivals_distance_from_first_job (idx : ℕ)
    (h : idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2) :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≥ 1 →
    arrival_times_are_consistent job_arrival arr_seq →
    arrival_sequence_is_a_set arr_seq →
    sporadic_task_model task_period job_arrival job_task arr_seq →
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx) ≥
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0) +
    idx * task_period tsk := by
  intro _GE1 CONS SET SPO
  induction idx with
  | zero => simp only [Nat.zero_mul, Nat.add_zero]; exact Nat.le_refl _
  | succ n ih =>
    have h_n_lt : n < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 := by omega
    have h_n_pred : n < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1 := by omega
    have h_sep := sorted_arrivals_separated_by_period task_period job_arrival job_jitter job_task arr_seq tsk t1 t2 elem n h_n_pred CONS SET SPO
    have h_ih := ih h_n_lt
    calc job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem (n + 1))
        ≥ job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem n) + task_period tsk := h_sep
      _ ≥ (job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0) + n * task_period tsk) + task_period tsk := Nat.add_le_add_right h_ih _
      _ = job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0) + (n + 1) * task_period tsk := by ring

theorem sorted_arrivals_distance_between_first_and_last :
    num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 ≥ 1 →
    arrival_times_are_consistent job_arrival arr_seq →
    arrival_sequence_is_a_set arr_seq →
    sporadic_task_model task_period job_arrival job_task arr_seq →
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem
      (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1)) ≥
    job_arrival (nth_job job_arrival job_jitter job_task arr_seq tsk t1 t2 elem 0) +
    (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) * task_period tsk := by
  intro GE1 CONS SET SPO
  apply sorted_arrivals_distance_from_first_job task_period job_arrival job_jitter job_task arr_seq tsk t1 t2 elem _ _ GE1 CONS SET SPO
  omega

end FirstAndLastJobs

end DistanceBetweenSporadicJobs

end Prosa.Classic.Model.Arrival.Jitter.Task_arrival
