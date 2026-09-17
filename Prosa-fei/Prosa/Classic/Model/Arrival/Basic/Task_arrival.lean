-- Translated from: ../rt-proofs/classic/model/arrival/basic/task_arrival.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Data.List.Sort

namespace Prosa.Classic.Model.Arrival.Basic.Task_arrival

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

section ArrivalModels

variable {Task : Type _} [DecidableEq Task]
variable (task_period : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)

def sporadic_task_model :=
  ∀ (j j' : Job),
    j ≠ j' →
    arrives_in arr_seq j →
    arrives_in arr_seq j' →
    job_task j = job_task j' →
    job_arrival j ≤ job_arrival j' →
    job_arrival j' ≥ job_arrival j + task_period (job_task j)

end ArrivalModels

section NumberOfArrivals

variable {Task : Type _} [DecidableEq Task]
variable {Job : Type _} [DecidableEq Job]
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)

variable (tsk : Task)

def is_job_of_task (j : Job) : Bool := decide (job_task j = tsk)

def arrivals_of_task_between (t1 t2 : Time) :=
  (jobs_arrived_between arr_seq t1 t2).filter (is_job_of_task job_task tsk)

def arrivals_of_task_before (t : Time) :=
  arrivals_of_task_between job_task arr_seq tsk 0 t

def num_arrivals_of_task (t1 t2 : Time) :=
  (arrivals_of_task_between job_task arr_seq tsk t1 t2).length

section Lemmas

theorem num_arrivals_of_task_cat (t t1 t2 : Time)
    (h : t1 ≤ t ∧ t ≤ t2) :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 =
    num_arrivals_of_task job_task arr_seq tsk t1 t +
    num_arrivals_of_task job_task arr_seq tsk t t2 := by
  simp only [num_arrivals_of_task, arrivals_of_task_between]
  rw [job_arrived_between_cat arr_seq t1 t t2 h.1 h.2]
  rw [List.filter_append, List.length_append]

end Lemmas

end NumberOfArrivals

section DistanceBetweenSporadicJobs

variable {Task : Type _} [DecidableEq Task]
variable (task_period : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : arrival_sequence Job)

variable (tsk : Task)

variable (t1 t2 : Time)

variable (elem : Job)

private noncomputable def sorted_jobs_aux :=
  (arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
    (fun j j' => decide (job_arrival j ≤ job_arrival j'))

private noncomputable def nth_job_aux (i : ℕ) :=
  (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).getD i elem

theorem sorted_arrivals_properties_of_nth (idx : ℕ)
    (h : idx < num_arrivals_of_task job_task arr_seq tsk t1 t2) :
    arrival_times_are_consistent job_arrival arr_seq →
    t1 ≤ job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx) ∧
    job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx) < t2 ∧
    job_task (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx) = tsk ∧
    arrives_in arr_seq (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx) := by
  intro CONS
  set nj := nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx
  have h_len : idx < (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).length := by
    simp only [sorted_jobs_aux, List.length_mergeSort]
    exact h
  have h_in_sorted : nj ∈ sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2 := by
    simp only [nj, nth_job_aux]
    unfold List.getD
    simp [List.getElem?_eq_getElem h_len]
  have h_in_orig : nj ∈ arrivals_of_task_between job_task arr_seq tsk t1 t2 := by
    exact (List.mergeSort_perm _ _).mem_iff.mp h_in_sorted
  simp only [arrivals_of_task_between] at h_in_orig
  rw [List.mem_filter] at h_in_orig
  obtain ⟨h_jobs, h_task_bool⟩ := h_in_orig
  have h_task_eq : job_task nj = tsk := by
    simp only [is_job_of_task] at h_task_bool
    rwa [decide_eq_true_eq] at h_task_bool
  have h_arrived : arrives_in arr_seq nj :=
    in_arrivals_implies_arrived job_arrival arr_seq CONS nj t1 t2 h_jobs
  have h_between : arrived_between job_arrival nj t1 t2 :=
    in_arrivals_implies_arrived_between job_arrival arr_seq CONS nj t1 t2 h_jobs
  exact ⟨h_between.1, h_between.2, h_task_eq, h_arrived⟩

theorem sorted_arrivals_current_differs_from_next (idx : ℕ)
    (h : idx < num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) :
    arrival_times_are_consistent job_arrival arr_seq →
    arrival_sequence_is_a_set arr_seq →
    nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx ≠
    nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem (idx + 1) := by
  intro CONS SET
  have h_len_eq : (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).length =
      num_arrivals_of_task job_task arr_seq tsk t1 t2 := by
    simp only [sorted_jobs_aux, List.length_mergeSort]; rfl
  have h_nodup_orig : (arrivals_of_task_between job_task arr_seq tsk t1 t2).Nodup := by
    simp only [arrivals_of_task_between]
    exact List.Nodup.filter _ (arrivals_uniq job_arrival arr_seq CONS SET t1 t2)
  have h_nodup : (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).Nodup :=
    (List.mergeSort_perm _ _).nodup_iff.mpr h_nodup_orig
  have h_idx_lt : idx < (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).length := by omega
  have h_idx1_lt : idx + 1 < (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).length := by omega
  intro heq
  simp only [nth_job_aux] at heq
  have h1 : (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).getD idx elem =
      (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2)[idx] :=
    (List.getElem_eq_getD elem).symm
  have h2 : (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).getD (idx + 1) elem =
      (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2)[idx + 1] :=
    (List.getElem_eq_getD elem).symm
  rw [h1, h2] at heq
  exact absurd ((List.Nodup.getElem_inj_iff h_nodup).mp heq) (by omega)

theorem sorted_arrivals_separated_by_period (idx : ℕ)
    (h : idx < num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) :
    arrival_times_are_consistent job_arrival arr_seq →
    arrival_sequence_is_a_set arr_seq →
    sporadic_task_model task_period job_arrival job_task arr_seq →
    job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem (idx + 1)) ≥
    job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx) +
    task_period tsk := by
  intro CONS SET SPO
  have h_idx_lt : idx < num_arrivals_of_task job_task arr_seq tsk t1 t2 := by omega
  have h_idx1_lt : idx + 1 < num_arrivals_of_task job_task arr_seq tsk t1 t2 := by omega
  have NTH := sorted_arrivals_properties_of_nth job_arrival job_task arr_seq tsk t1 t2 elem idx h_idx_lt CONS
  have NTH1 := sorted_arrivals_properties_of_nth job_arrival job_task arr_seq tsk t1 t2 elem (idx + 1) h_idx1_lt CONS
  have NEQ := sorted_arrivals_current_differs_from_next job_arrival job_task arr_seq tsk t1 t2 elem idx h CONS SET
  -- Show the sorted order implies arrival time ordering
  have h_le : job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx) ≤
      job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem (idx + 1)) := by
    have h_perm : (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).Perm
        (arrivals_of_task_between job_task arr_seq tsk t1 t2) :=
      List.mergeSort_perm _ _
    have h_len_eq : (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).length =
        (arrivals_of_task_between job_task arr_seq tsk t1 t2).length :=
      h_perm.length_eq
    have h_sj_idx : idx < (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).length := by
      simp only [num_arrivals_of_task] at h_idx_lt; rw [h_len_eq]; exact h_idx_lt
    have h_sj_idx1 : idx + 1 < (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).length := by
      simp only [num_arrivals_of_task] at h_idx1_lt; rw [h_len_eq]; exact h_idx1_lt
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
    have h_sorted : (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).Pairwise
        (fun a b => decide (job_arrival a ≤ job_arrival b) = true) :=
      List.pairwise_mergeSort h_trans h_total _
    simp only [nth_job_aux]
    have h1 : (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).getD idx elem =
        (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2)[idx] :=
      (List.getElem_eq_getD elem).symm
    have h2 : (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2).getD (idx + 1) elem =
        (sorted_jobs_aux job_arrival job_task arr_seq tsk t1 t2)[idx + 1] :=
      (List.getElem_eq_getD elem).symm
    rw [h1, h2]
    have := List.pairwise_iff_getElem.mp h_sorted idx (idx + 1) h_sj_idx h_sj_idx1 (by omega)
    rw [decide_eq_true_eq] at this; exact this
  -- Apply sporadic model
  have h_task_eq : job_task (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx) =
      job_task (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem (idx + 1)) := by
    rw [NTH.2.2.1, NTH1.2.2.1]
  have := SPO _ _ NEQ NTH.2.2.2 NTH1.2.2.2 h_task_eq h_le
  rw [NTH.2.2.1] at this
  exact this

section FirstAndLastJobs

theorem sorted_arrivals_distance_from_first_job (idx : ℕ)
    (h : idx < num_arrivals_of_task job_task arr_seq tsk t1 t2) :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 ≥ 1 →
    arrival_times_are_consistent job_arrival arr_seq →
    arrival_sequence_is_a_set arr_seq →
    sporadic_task_model task_period job_arrival job_task arr_seq →
    job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem idx) ≥
    job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem 0) +
    idx * task_period tsk := by
  intro _GE1 CONS SET SPO
  induction idx with
  | zero => simp
  | succ n ih =>
    have h_n_lt : n < num_arrivals_of_task job_task arr_seq tsk t1 t2 := by omega
    have h_n_pred : n < num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1 := by omega
    have h_sep := sorted_arrivals_separated_by_period task_period job_arrival job_task arr_seq tsk t1 t2 elem n h_n_pred CONS SET SPO
    have h_ih := ih h_n_lt
    calc job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem (n + 1))
        ≥ job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem n) + task_period tsk := h_sep
      _ ≥ (job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem 0) + n * task_period tsk) + task_period tsk := Nat.add_le_add_right h_ih _
      _ = job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem 0) + (n + 1) * task_period tsk := by ring

theorem sorted_arrivals_distance_between_first_and_last :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 ≥ 1 →
    arrival_times_are_consistent job_arrival arr_seq →
    arrival_sequence_is_a_set arr_seq →
    sporadic_task_model task_period job_arrival job_task arr_seq →
    job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem
      (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1)) ≥
    job_arrival (nth_job_aux job_arrival job_task arr_seq tsk t1 t2 elem 0) +
    (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) * task_period tsk := by
  intro GE1 CONS SET SPO
  apply sorted_arrivals_distance_from_first_job task_period job_arrival job_task arr_seq tsk t1 t2 elem _ _ GE1 CONS SET SPO
  omega

end FirstAndLastJobs

end DistanceBetweenSporadicJobs

end Prosa.Classic.Model.Arrival.Basic.Task_arrival
