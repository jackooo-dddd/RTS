-- Translated from: ../rt-proofs/classic/model/arrival/basic/arrival_sequence.v
import Prosa.Util.Bigcat
import Prosa.Classic.Model.Time
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

namespace Prosa.Classic.Model.Arrival.Basic.Arrival_sequence

open Prosa.Classic.Model.Time
open Prosa.Util.Bigcat

section ArrivalSequenceDef

variable (Job : Type _) [DecidableEq Job]

def arrival_sequence := Time → List Job

end ArrivalSequenceDef

section JobProperties

variable {Job : Type _} [DecidableEq Job]
variable (arr_seq : arrival_sequence Job)

def jobs_arriving_at (t : Time) := arr_seq t

def arrives_at (j : Job) (t : Time) := j ∈ jobs_arriving_at arr_seq t

def arrives_in (j : Job) := ∃ t, j ∈ jobs_arriving_at arr_seq t

end JobProperties

section ArrivalSequenceProperties

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (arr_seq : arrival_sequence Job)

def arrival_times_are_consistent :=
  ∀ j t, arrives_at arr_seq j t → job_arrival j = t

def arrival_sequence_is_a_set := ∀ t, (jobs_arriving_at arr_seq t).Nodup

end ArrivalSequenceProperties

section PropertiesOfArrivalTime

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (j : Job)

def has_arrived (t : Time) := job_arrival j ≤ t

def arrived_before (t : Time) := job_arrival j < t

def arrived_between (t1 t2 : Time) := t1 ≤ job_arrival j ∧ job_arrival j < t2

end PropertiesOfArrivalTime

section ArrivalSequencePrefix

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (arr_seq : arrival_sequence Job)

def jobs_arrived_between (t1 t2 : Time) : List Job :=
  bigcat_nat (jobs_arriving_at arr_seq) t1 t2

def jobs_arrived_up_to (t : Time) : List Job :=
  jobs_arrived_between arr_seq 0 (t + 1)

def jobs_arrived_before (t : Time) : List Job :=
  jobs_arrived_between arr_seq 0 t

section Lemmas

section Basic

theorem job_arrived_between_cat (t1 t t2 : Time)
    (h1 : t1 ≤ t) (h2 : t ≤ t2) :
    jobs_arrived_between arr_seq t1 t2 =
    jobs_arrived_between arr_seq t1 t ++ jobs_arrived_between arr_seq t t2 := by
  simp only [jobs_arrived_between, bigcat_nat]
  have h_split : List.range' t1 (t2 - t1) =
      List.range' t1 (t - t1) ++ List.range' t (t2 - t) := by
    have h_app := @List.range'_append t1 (t - t1) (t2 - t) 1
    simp only [Nat.one_mul] at h_app
    have heq1 : t1 + (t - t1) = t := Nat.add_sub_cancel' h1
    have heq2 : t - t1 + (t2 - t) = t2 - t1 := by
      rw [Nat.add_comm]; exact Nat.sub_add_sub_cancel h2 h1
    rw [heq1, heq2] at h_app
    exact h_app.symm
  rw [h_split, List.map_append, List.flatten_append]

theorem jobs_arrived_between_mem_cat (j : Job) (t1 t t2 : Time)
    (h1 : t1 ≤ t) (h2 : t ≤ t2) :
    j ∈ jobs_arrived_between arr_seq t1 t2 ↔
    j ∈ (jobs_arrived_between arr_seq t1 t ++ jobs_arrived_between arr_seq t t2) := by
  rw [job_arrived_between_cat arr_seq t1 t t2 h1 h2]

theorem jobs_arrived_between_sub (j : Job) (t1 t1' t2 t2' : Time)
    (h1 : t1' ≤ t1) (h2 : t2 ≤ t2')
    (h_in : j ∈ jobs_arrived_between arr_seq t1 t2) :
    j ∈ jobs_arrived_between arr_seq t1' t2' := by
  unfold jobs_arrived_between at h_in ⊢
  obtain ⟨i, hi_mem, hi_ge, hi_lt⟩ := mem_bigcat_nat_exists j t1 t2 _ h_in
  have h_ge' : t1' ≤ i := Nat.le_trans h1 hi_ge
  have h_lt' : i < t2' := Nat.lt_of_lt_of_le hi_lt h2
  exact mem_bigcat_nat j t1' t2' i _ ⟨h_ge', h_lt'⟩ hi_mem

end Basic

section ArrivalTimes

variable (H_arrival_times_are_consistent :
  arrival_times_are_consistent job_arrival arr_seq)

include H_arrival_times_are_consistent

theorem in_arrivals_implies_arrived (j : Job) (t1 t2 : Time)
    (h_in : j ∈ jobs_arrived_between arr_seq t1 t2) :
    arrives_in arr_seq j := by
  have ⟨i, hi_mem, _, _⟩ := mem_bigcat_nat_exists j t1 t2 _ h_in
  exact ⟨i, hi_mem⟩

theorem in_arrivals_implies_arrived_between (j : Job) (t1 t2 : Time)
    (h_in : j ∈ jobs_arrived_between arr_seq t1 t2) :
    arrived_between job_arrival j t1 t2 := by
  have ⟨i, hi_mem, hi_ge, hi_lt⟩ := mem_bigcat_nat_exists j t1 t2 _ h_in
  have h_cons := H_arrival_times_are_consistent j i hi_mem
  simp only [arrived_between, h_cons]
  exact ⟨hi_ge, hi_lt⟩

theorem in_arrivals_implies_arrived_before (j : Job) (t : Time)
    (h_in : j ∈ jobs_arrived_before arr_seq t) :
    arrived_before job_arrival j t := by
  have h := in_arrivals_implies_arrived_between job_arrival arr_seq H_arrival_times_are_consistent j 0 t h_in
  exact h.2

theorem arrived_between_implies_in_arrivals (j : Job) (t1 t2 : Time)
    (h_arrives : arrives_in arr_seq j)
    (h_between : arrived_between job_arrival j t1 t2) :
    j ∈ jobs_arrived_between arr_seq t1 t2 := by
  obtain ⟨a_j, h_arr⟩ := h_arrives
  have h_same := H_arrival_times_are_consistent j a_j h_arr
  subst h_same
  unfold jobs_arrived_between
  exact mem_bigcat_nat j t1 t2 (job_arrival j) (jobs_arriving_at arr_seq) ⟨h_between.1, h_between.2⟩ h_arr

theorem arrivals_uniq
    (h_set : arrival_sequence_is_a_set arr_seq)
    (t1 t2 : Time) :
    (jobs_arrived_between arr_seq t1 t2).Nodup := by
  apply bigcat_nat_uniq
  · intro i; exact h_set i
  · intro x i1 i2 h1 h2
    exact (H_arrival_times_are_consistent x i1 h1).symm.trans (H_arrival_times_are_consistent x i2 h2)

end ArrivalTimes

end Lemmas

end ArrivalSequencePrefix

end Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
