-- Translated from: ../rt-proofs/classic/model/arrival/jitter/arrival_sequence.v
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Mathlib.Data.List.Basic

namespace Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

section ActualArrival

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_jitter : Job → Time)
variable (j : Job)

def actual_arrival := job_arrival j + job_jitter j

def jitter_has_passed (t : Time) := actual_arrival job_arrival job_jitter j ≤ t

def actual_arrival_before (t : Time) := actual_arrival job_arrival job_jitter j < t

def actual_arrival_between (t1 t2 : Time) :=
  t1 ≤ actual_arrival job_arrival job_jitter j ∧ actual_arrival job_arrival job_jitter j < t2

end ActualArrival

section ArrivingJobs

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_jitter : Job → Time)
variable (arr_seq : arrival_sequence Job)

noncomputable def actual_arrivals_between (t1 t2 : Time) : List Job :=
  (jobs_arrived_before arr_seq t2).filter
    (fun j => decide (t1 ≤ actual_arrival job_arrival job_jitter j ∧
              actual_arrival job_arrival job_jitter j < t2))

noncomputable def actual_arrivals_up_to (t : Time) : List Job :=
  actual_arrivals_between job_arrival job_jitter arr_seq 0 (t + 1)

noncomputable def actual_arrivals_before (t : Time) : List Job :=
  actual_arrivals_between job_arrival job_jitter arr_seq 0 t

section Lemmas

variable (H_arrival_times_are_consistent :
  arrival_times_are_consistent job_arrival arr_seq)

include H_arrival_times_are_consistent

section Basic

theorem actual_arrivals_between_mem_cat (j : Job) (t1 t t2 : Time)
    (h1 : t1 ≤ t) (h2 : t ≤ t2) :
    j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2 ↔
    j ∈ (actual_arrivals_between job_arrival job_jitter arr_seq t1 t ++
         actual_arrivals_between job_arrival job_jitter arr_seq t t2) := by
  simp only [actual_arrivals_between]
  constructor
  · intro h_in
    rw [List.mem_filter] at h_in
    obtain ⟨h_mem, h_pred⟩ := h_in
    simp only [decide_eq_true_eq] at h_pred
    obtain ⟨h_ge, h_lt⟩ := h_pred
    rw [List.mem_append]
    by_cases h_case : actual_arrival job_arrival job_jitter j < t
    · left
      rw [List.mem_filter]
      constructor
      · have h_arrives : arrives_in arr_seq j :=
          in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j 0 t2 h_mem
        have h_le_aa : job_arrival j ≤ actual_arrival job_arrival job_jitter j :=
           Nat.le_add_right _ _
        have h_lt' : job_arrival j < t :=
           Nat.lt_of_le_of_lt h_le_aa h_case
        apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 t h_arrives
        exact ⟨Nat.zero_le _, h_lt'⟩
      · simp only [decide_eq_true_eq]
        exact ⟨h_ge, h_case⟩
    · right
      rw [List.mem_filter]
      constructor
      · exact h_mem
      · simp only [decide_eq_true_eq]
        push_neg at h_case
        exact ⟨h_case, h_lt⟩
  · intro h_in
    rw [List.mem_append] at h_in
    rw [List.mem_filter]
    cases h_in with
    | inl h_left =>
      rw [List.mem_filter] at h_left
      obtain ⟨h_mem, h_pred⟩ := h_left
      simp only [decide_eq_true_eq] at h_pred
      obtain ⟨h_ge, h_lt⟩ := h_pred
      constructor
      · have h_arrives : arrives_in arr_seq j :=
          in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j 0 t h_mem
        have h_le_aa : job_arrival j ≤ actual_arrival job_arrival job_jitter j :=
           Nat.le_add_right _ _
        have h_lt' : job_arrival j < t2 :=
           Nat.lt_of_le_of_lt h_le_aa (Nat.lt_of_lt_of_le h_lt h2)
        apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 t2 h_arrives
        exact ⟨Nat.zero_le _, h_lt'⟩
      · simp only [decide_eq_true_eq]
        exact ⟨h_ge, Nat.lt_of_lt_of_le h_lt h2⟩
    | inr h_right =>
      rw [List.mem_filter] at h_right
      obtain ⟨h_mem, h_pred⟩ := h_right
      simp only [decide_eq_true_eq] at h_pred
      obtain ⟨h_ge, h_lt⟩ := h_pred
      constructor
      · exact h_mem
      · simp only [decide_eq_true_eq]
        exact ⟨Nat.le_trans h1 h_ge, h_lt⟩

theorem actual_arrivals_between_sub (j : Job) (t1 t1' t2 t2' : Time)
    (h1 : t1' ≤ t1) (h2 : t2 ≤ t2')
    (h_in : j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2) :
    j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1' t2' := by
  simp only [actual_arrivals_between] at h_in ⊢
  rw [List.mem_filter] at h_in ⊢
  obtain ⟨h_mem, h_pred⟩ := h_in
  simp only [decide_eq_true_eq] at h_pred ⊢
  obtain ⟨h_ge, h_lt⟩ := h_pred
  constructor
  · have h_arrives : arrives_in arr_seq j :=
      in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j 0 t2 h_mem
    have h_le_aa : job_arrival j ≤ actual_arrival job_arrival job_jitter j :=
       Nat.le_add_right _ _
    have h_lt' : job_arrival j < t2' :=
       Nat.lt_of_le_of_lt h_le_aa (Nat.lt_of_lt_of_le h_lt h2)
    apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 t2' h_arrives
    exact ⟨Nat.zero_le _, h_lt'⟩
  · exact ⟨Nat.le_trans h1 h_ge, Nat.lt_of_lt_of_le h_lt h2⟩

end Basic

section ArrivalTimes

theorem in_actual_arrivals_between_implies_arrived (j : Job) (t1 t2 : Time)
    (h_in : j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2) :
    arrives_in arr_seq j := by
  simp only [actual_arrivals_between] at h_in
  have h_mem := List.mem_of_mem_filter h_in
  exact in_arrivals_implies_arrived job_arrival arr_seq H_arrival_times_are_consistent j 0 t2 h_mem

theorem in_actual_arrivals_before_implies_arrived (j : Job) (t : Time)
    (h_in : j ∈ actual_arrivals_before job_arrival job_jitter arr_seq t) :
    arrives_in arr_seq j := by
  exact in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq H_arrival_times_are_consistent j 0 t h_in

theorem in_actual_arrivals_implies_arrived_before (j : Job) (t : Time)
    (h_in : j ∈ actual_arrivals_before job_arrival job_jitter arr_seq t) :
    actual_arrival_before job_arrival job_jitter j t := by
  simp only [actual_arrivals_before, actual_arrivals_between] at h_in
  have h_pred := (List.mem_filter.mp h_in).2
  simp only [decide_eq_true_eq] at h_pred
  exact h_pred.2

theorem in_actual_arrivals_implies_arrived_between (j : Job) (t1 t2 : Time)
    (h_in : j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2) :
    actual_arrival_between job_arrival job_jitter j t1 t2 := by
  simp only [actual_arrivals_between] at h_in
  have h_pred := (List.mem_filter.mp h_in).2
  simp only [decide_eq_true_eq] at h_pred
  exact h_pred

theorem arrived_between_implies_in_actual_arrivals (j : Job) (t1 t2 : Time)
    (h_arrives : arrives_in arr_seq j)
    (h_between : actual_arrival_between job_arrival job_jitter j t1 t2) :
    j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2 := by
  simp only [actual_arrivals_between]
  rw [List.mem_filter]
  constructor
  · have h_le_aa : job_arrival j ≤ actual_arrival job_arrival job_jitter j :=
       Nat.le_add_right _ _
    have h_lt : job_arrival j < t2 :=
       Nat.lt_of_le_of_lt h_le_aa h_between.2
    apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 t2 h_arrives
    exact ⟨Nat.zero_le _, h_lt⟩
  · simp only [decide_eq_true_eq]
    exact h_between

theorem actual_arrivals_uniq
    (h_set : arrival_sequence_is_a_set arr_seq)
    (t1 t2 : Time) :
    (actual_arrivals_between job_arrival job_jitter arr_seq t1 t2).Nodup := by
  simp only [actual_arrivals_between]
  apply List.Nodup.filter
  exact arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent h_set 0 t2

end ArrivalTimes

end Lemmas

end ArrivingJobs

end Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
