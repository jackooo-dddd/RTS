-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/arrival/jitter/arrival_sequence.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 30)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence

/-!
Job arrival sequences with jitter (Rocq module `ArrivalSequenceWithJitter`, which `Export`s
`ArrivalSequence`).

Representation notes (as in the accepted `classic/model/arrival/basic/arrival_sequence.v`):
* Boolean tests in proposition position are `= true`; `j \in s` returning `bool` is `decide (j ∈ s)`,
  inside propositions `j ∈ s`; Boolean range tests `t1 <= x < t2` are `decide (t1 ≤ x) && decide (x < t2)`;
  `[seq j <- s | P j]` is `s.filter P`; `uniq` is `Nodup`.
* `actual_arrival` returns `nat` in the source (the sum of two `time`s), hence `Nat` here.
* The section-local `Let`s (`actual_job_arrival`, `actual_job_arrival_between`, `actual_job_arrival_before`,
  `arrivals_before`) are unfolded.
* Binder lists follow the Rocq contract: the consistency hypothesis is taken only by the lemmas whose proof
  uses it (`actual_arrivals_between_mem_cat`, `actual_arrivals_between_sub`,
  `arrived_between_implies_in_actual_arrivals`, `actual_arrivals_uniq`).
-/

namespace Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Util.Bigcat (mem_bigcat_nat_exists)

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def actual_arrival {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time) (j : Job) : Nat :=
  job_arrival j + job_jitter j

def jitter_has_passed {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time) (j : Job)
    (t : time) : Bool :=
  decide (actual_arrival job_arrival job_jitter j ≤ t)

def actual_arrival_before {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time) (j : Job)
    (t : time) : Bool :=
  decide (actual_arrival job_arrival job_jitter j < t)

def actual_arrival_between {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time) (j : Job)
    (t1 t2 : time) : Bool :=
  decide (t1 ≤ actual_arrival job_arrival job_jitter j) && decide (actual_arrival job_arrival job_jitter j < t2)

def actual_arrivals_between {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (t1 t2 : time) : List Job :=
  (jobs_arrived_before arr_seq t2).filter (fun j =>
    decide (t1 ≤ actual_arrival job_arrival job_jitter j) && decide (actual_arrival job_arrival job_jitter j < t2))

def actual_arrivals_up_to {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (t : time) : List Job :=
  actual_arrivals_between job_arrival job_jitter arr_seq 0 (t + 1)

def actual_arrivals_before {Job : Type u} [DecidableEq Job] (job_arrival job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (t : time) : List Job :=
  actual_arrivals_between job_arrival job_jitter arr_seq 0 t

/-- LEAN_HELPER: membership in `actual_arrivals_between`. -/
private theorem mem_actual_arrivals_between {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (arr_seq : arrival_sequence Job) (j : Job) (t1 t2 : time) :
    j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2 ↔
      (t1 ≤ actual_arrival job_arrival job_jitter j ∧ actual_arrival job_arrival job_jitter j < t2) ∧
        j ∈ jobs_arrived_before arr_seq t2 := by
  simp [actual_arrivals_between, List.mem_filter, and_comm]

theorem actual_arrivals_between_mem_cat {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) :
    ∀ (j : Job) (t1 t t2 : Nat),
      t1 ≤ t →
      t ≤ t2 →
      decide (j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2) =
        decide (j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t ++
          actual_arrivals_between job_arrival job_jitter arr_seq t t2) := by
  intro j t1 t t2 GE LE
  have hin : ∀ T, arrives_in arr_seq j → actual_arrival job_arrival job_jitter j < T →
      j ∈ jobs_arrived_before arr_seq T := by
    intro T ARR LT
    apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 T ARR
    simp only [arrived_between, actual_arrival] at LT ⊢
    simp; omega'
  have harr : ∀ T, j ∈ jobs_arrived_before arr_seq T → arrives_in arr_seq j :=
    fun T h => in_arrivals_implies_arrived arr_seq j 0 T h
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, List.mem_append, mem_actual_arrivals_between]
  constructor
  · rintro ⟨⟨h1, h2⟩, IN⟩
    rcases Nat.lt_or_ge (actual_arrival job_arrival job_jitter j) t with h | h
    · exact Or.inl ⟨⟨h1, h⟩, hin t (harr _ IN) h⟩
    · exact Or.inr ⟨⟨h, h2⟩, IN⟩
  · rintro (⟨⟨h1, h2⟩, IN⟩ | ⟨⟨h1, h2⟩, IN⟩)
    · exact ⟨⟨h1, by omega'⟩, hin t2 (harr _ IN) (by omega')⟩
    · exact ⟨⟨by omega', h2⟩, IN⟩

theorem actual_arrivals_between_sub {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) :
    ∀ (j : Job) (t1 t1' t2 t2' : Nat),
      t1' ≤ t1 →
      t2 ≤ t2' →
      j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2 →
      j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1' t2' := by
  intro j t1 t1' t2 t2' GE1 LE2 IN
  rw [mem_actual_arrivals_between] at IN ⊢
  obtain ⟨⟨h1, h2⟩, IN⟩ := IN
  refine ⟨⟨by omega', by omega'⟩, ?_⟩
  apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 t2'
    (in_arrivals_implies_arrived arr_seq j 0 t2 IN)
  simp only [arrived_between, actual_arrival] at h2 ⊢
  simp; omega'

theorem in_actual_arrivals_between_implies_arrived {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t1 t2 : time),
      j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2 →
      arrives_in arr_seq j := by
  intro j t1 t2 IN
  rw [mem_actual_arrivals_between] at IN
  exact in_arrivals_implies_arrived arr_seq j 0 t2 IN.2

theorem in_actual_arrivals_before_implies_arrived {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t : time),
      j ∈ actual_arrivals_before job_arrival job_jitter arr_seq t →
      arrives_in arr_seq j := by
  intro j t IN
  exact in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq j 0 t IN

theorem in_actual_arrivals_implies_arrived_before {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t : time),
      j ∈ actual_arrivals_before job_arrival job_jitter arr_seq t →
      actual_arrival_before job_arrival job_jitter j t = true := by
  intro j t IN
  rw [actual_arrivals_before, mem_actual_arrivals_between] at IN
  simp [actual_arrival_before, IN.1.2]

theorem in_actual_arrivals_implies_arrived_between {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t1 t2 : time),
      j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2 →
      actual_arrival_between job_arrival job_jitter j t1 t2 = true := by
  intro j t1 t2 IN
  rw [mem_actual_arrivals_between] at IN
  simp [actual_arrival_between, IN.1.1, IN.1.2]

theorem arrived_between_implies_in_actual_arrivals {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) :
    ∀ (j : Job) (t1 t2 : time),
      arrives_in arr_seq j →
      actual_arrival_between job_arrival job_jitter j t1 t2 = true →
      j ∈ actual_arrivals_between job_arrival job_jitter arr_seq t1 t2 := by
  intro j t1 t2 IN BEFORE
  simp only [actual_arrival_between, Bool.and_eq_true, decide_eq_true_eq] at BEFORE
  rw [mem_actual_arrivals_between]
  refine ⟨BEFORE, ?_⟩
  apply arrived_between_implies_in_arrivals job_arrival arr_seq H_arrival_times_are_consistent j 0 t2 IN
  simp only [arrived_between, actual_arrival] at BEFORE ⊢
  simp; omega'

theorem actual_arrivals_uniq {Job : Type u} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) :
    arrival_sequence_is_a_set arr_seq →
    ∀ t1 t2 : time, (actual_arrivals_between job_arrival job_jitter arr_seq t1 t2).Nodup := by
  intro SET t1 t2
  exact (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent SET 0 t2).filter _

end Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
