-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/arrival/basic/arrival_sequence.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 23)

import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Util.Notation
import Prosa.Util.Bigcat

/-!
Job arrival sequences (Rocq module `ArrivalSequence`, which `Export`s `Time`).

Representation notes:
* `arrival_sequence Job := time → seq Job` is `time → List Job`.
* `j \in s` returning `bool` is `decide (j ∈ s)`; inside propositions it is
  `j ∈ s`; Boolean range tests `t1 <= x < t2` are
  `decide (t1 ≤ x) && decide (x < t2)`.
* `\cat_(t1 <= t < t2) F t` is the accepted v0.6 helper
  `Prosa.Util.Notation.bigCat t1 t2 F` (as in the v0.6 `arrivals_between`).
* Binder lists follow the Rocq contract: e.g. `in_arrivals_implies_arrived` does
  not take the consistency hypothesis (its proof term does not use it), while
  the other prefix lemmas take `job_arrival arr_seq H_arrival_times_are_consistent`.
-/


/- The Rocq module path is mirrored exactly, which repeats a namespace segment
(file `X` containing Rocq `Module X`); this is intentional. -/
set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence

export Prosa.Classic.Model.Time.Time (time duration instant)

open Prosa.Classic.Model.Time.Time
open Prosa.Util.Notation (bigCat)
open Prosa.Util.Bigcat (mem_bigcat_nat mem_bigcat_nat_exists bigcat_nat_uniq)

universe u

/-- An arrival sequence maps each time to the (finite) sequence of jobs arriving then. -/
abbrev arrival_sequence (Job : Type u) [DecidableEq Job] := time → List Job

def jobs_arriving_at {Job : Type u} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (t : time) : List Job :=
  arr_seq t

def arrives_at {Job : Type u} [DecidableEq Job] (arr_seq : arrival_sequence Job) (j : Job)
    (t : time) : Bool :=
  decide (j ∈ jobs_arriving_at arr_seq t)

def arrives_in {Job : Type u} [DecidableEq Job] (arr_seq : arrival_sequence Job) (j : Job) :
    Prop :=
  ∃ t, j ∈ jobs_arriving_at arr_seq t

def arrival_times_are_consistent {Job : Type u} [DecidableEq Job] (job_arrival : Job → time)
    (arr_seq : arrival_sequence Job) : Prop :=
  ∀ j t, arrives_at arr_seq j t = true → job_arrival j = t

def arrival_sequence_is_a_set {Job : Type u} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) : Prop :=
  ∀ t, (jobs_arriving_at arr_seq t).Nodup

def has_arrived {Job : Type u} [DecidableEq Job] (job_arrival : Job → time) (j : Job)
    (t : time) : Bool :=
  decide (job_arrival j ≤ t)

def arrived_before {Job : Type u} [DecidableEq Job] (job_arrival : Job → time) (j : Job)
    (t : time) : Bool :=
  decide (job_arrival j < t)

def arrived_between {Job : Type u} [DecidableEq Job] (job_arrival : Job → time) (j : Job)
    (t1 t2 : time) : Bool :=
  decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)

def jobs_arrived_between {Job : Type u} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (t1 t2 : time) : List Job :=
  bigCat t1 t2 (fun t => jobs_arriving_at arr_seq t)

def jobs_arrived_up_to {Job : Type u} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (t : time) : List Job :=
  jobs_arrived_between arr_seq 0 (t + 1)

def jobs_arrived_before {Job : Type u} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (t : time) : List Job :=
  jobs_arrived_between arr_seq 0 t

/-- LEAN_HELPER: splitting a nat-indexed big concatenation (same proof as the
private v0.6 helper in `Prosa.Analysis.Facts.Behavior.Arrivals`). -/
private theorem bigCat_split {α : Type u} (F : Nat → List α) (t1 t t2 : Nat)
    (h1 : t1 ≤ t) (h2 : t ≤ t2) :
    bigCat t1 t2 F = bigCat t1 t F ++ bigCat t t2 F := by
  unfold bigCat
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h2
  have e1 : t1 + a + b - t1 = a + b := by omega
  have e2 : t1 + a - t1 = a := by omega
  have e3 : t1 + a + b - (t1 + a) = b := by omega
  rw [e1, e2, e3, List.range_add, List.map_append, List.flatten_append]
  congr 2
  simp only [List.map_map]
  congr 1
  funext i
  simp [Function.comp, Nat.add_assoc]

theorem job_arrived_between_cat {Job : Type u} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ t1 t t2 : Nat,
      t1 ≤ t →
      t ≤ t2 →
      jobs_arrived_between arr_seq t1 t2 =
        jobs_arrived_between arr_seq t1 t ++ jobs_arrived_between arr_seq t t2 := by
  intro t1 t t2 GE LE
  exact bigCat_split _ t1 t t2 GE LE

theorem jobs_arrived_between_mem_cat {Job : Type u} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t1 t t2 : Nat),
      t1 ≤ t →
      t ≤ t2 →
      decide (j ∈ jobs_arrived_between arr_seq t1 t2) =
        decide (j ∈ jobs_arrived_between arr_seq t1 t ++ jobs_arrived_between arr_seq t t2) := by
  intro j t1 t t2 GE LE
  rw [job_arrived_between_cat arr_seq t1 t t2 GE LE]

theorem jobs_arrived_between_sub {Job : Type u} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t1 t1' t2 t2' : Nat),
      t1' ≤ t1 →
      t2 ≤ t2' →
      j ∈ jobs_arrived_between arr_seq t1 t2 →
      j ∈ jobs_arrived_between arr_seq t1' t2' := by
  intro j t1 t1' t2 t2' GE1 LE2 IN
  obtain ⟨i, hi, h1, h2⟩ := mem_bigcat_nat_exists _ j t1 t2 IN
  exact mem_bigcat_nat _ j t1' t2' i ⟨by omega, by omega⟩ hi

theorem in_arrivals_implies_arrived {Job : Type u} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t1 t2 : time),
      j ∈ jobs_arrived_between arr_seq t1 t2 →
      arrives_in arr_seq j := by
  intro j t1 t2 IN
  obtain ⟨arr, hi, _, _⟩ := mem_bigcat_nat_exists _ j t1 t2 IN
  exact ⟨arr, hi⟩

theorem in_arrivals_implies_arrived_between {Job : Type u} [DecidableEq Job]
    (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) :
    ∀ (j : Job) (t1 t2 : time),
      j ∈ jobs_arrived_between arr_seq t1 t2 →
      arrived_between job_arrival j t1 t2 = true := by
  intro j t1 t2 IN
  obtain ⟨t0, hi, h1, h2⟩ := mem_bigcat_nat_exists _ j t1 t2 IN
  have := H_arrival_times_are_consistent j t0 (by simpa [arrives_at] using hi)
  simp [arrived_between, this, h1, h2]

theorem in_arrivals_implies_arrived_before {Job : Type u} [DecidableEq Job]
    (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) :
    ∀ (j : Job) (t : time),
      j ∈ jobs_arrived_before arr_seq t →
      arrived_before job_arrival j t = true := by
  intro j t IN
  have h := in_arrivals_implies_arrived_between job_arrival arr_seq
    H_arrival_times_are_consistent j 0 t IN
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at h
  simp [arrived_before, h.2]

theorem arrived_between_implies_in_arrivals {Job : Type u} [DecidableEq Job]
    (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) :
    ∀ (j : Job) (t1 t2 : time),
      arrives_in arr_seq j →
      arrived_between job_arrival j t1 t2 = true →
      j ∈ jobs_arrived_between arr_seq t1 t2 := by
  intro j t1 t2 ARR BEFORE
  obtain ⟨a_j, ARRj⟩ := ARR
  have SAME := H_arrival_times_are_consistent j a_j (by simpa [arrives_at] using ARRj)
  subst SAME
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at BEFORE
  exact mem_bigcat_nat _ j t1 t2 (job_arrival j) BEFORE ARRj

theorem arrivals_uniq {Job : Type u} [DecidableEq Job]
    (job_arrival : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) :
    arrival_sequence_is_a_set arr_seq →
    ∀ t1 t2 : time, (jobs_arrived_between arr_seq t1 t2).Nodup := by
  intro SET t1 t2
  apply bigcat_nat_uniq
  · exact SET
  · intro x t t' IN1 IN2
    have h1 := H_arrival_times_are_consistent x t (by simpa [arrives_at] using IN1)
    have h2 := H_arrival_times_are_consistent x t' (by simpa [arrives_at] using IN2)
    exact h1.symm.trans h2

end Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
