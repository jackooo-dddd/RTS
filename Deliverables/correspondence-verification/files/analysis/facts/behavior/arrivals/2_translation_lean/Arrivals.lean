-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/behavior/arrivals.v

import Prosa.Behavior.All
import Prosa.Util.All
import Prosa.Model.Task.Arrivals
import Prosa.Util.Bigcat

/-!
Every declaration takes exactly the binders of its elaborated v0.6 type, in
the same order (section hypotheses included), so binders are written per
declaration rather than through Lean section variables.
Representation: Boolean `x \in s` and `a <= b < c` in propositional position
are `decide (x ∈ s) = true` and `(decide (a ≤ b) && decide (b < c)) = true`;
`uniq` is `List.Nodup`; `sorted r` (adjacent pairs) is `List.IsChain (r · · = true)`;
`\cat_(x <- s) F x` is `bigCatSeqAll s F`.
-/

namespace Prosa.Analysis.Facts.Behavior.Arrivals

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Util.Notation
open Prosa.Util.Bigcat

/-- `nomega` after exposing the `instant`/`duration` aliases as `Nat`. -/
local macro "nomega" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Behavior.Time.instant, Prosa.Behavior.Time.duration] at *) <;> omega))

/-! ### Arrival predicates -/

theorem arrived_between_before {Job : JobType} [DecidableEq Job] [JobArrival Job] :
    ∀ (j : Job) (t1 t2 : instant),
      arrived_between j t1 t2 = true → arrived_before j t2 = true := by
  intro j t1 t2 h
  simp only [arrived_between, arrived_before, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  exact h.2

theorem arrived_before_has_arrived {Job : JobType} [DecidableEq Job] [JobArrival Job] :
    ∀ (j : Job) (t : instant), arrived_before j t = true → has_arrived j t = true := by
  intro j t h
  simp only [arrived_before, has_arrived, decide_eq_true_eq] at h ⊢
  nomega

theorem consistent_times_valid_arrival {Job : JobType} [DecidableEq Job] [JobArrival Job] :
    ∀ arr_seq : arrival_sequence Job,
      valid_arrival_sequence arr_seq → consistent_arrival_times arr_seq :=
  fun _ h => h.1

theorem uniq_valid_arrival {Job : JobType} [DecidableEq Job] [JobArrival Job] :
    ∀ arr_seq : arrival_sequence Job,
      valid_arrival_sequence arr_seq → arrival_sequence_uniq arr_seq :=
  fun _ h => h.2

/-! ### Arrived -/

theorem any_ready_job_is_pending {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [JobReady Job PState] :
    ∀ (j : Job) (t : instant), job_ready sched j t = true → pending sched j t = true :=
  fun j t h => ready_implies_pending sched j t h

theorem ready_implies_arrived {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [JobReady Job PState] :
    ∀ (j : Job) (t : instant), job_ready sched j t = true → has_arrived j t = true := by
  intro j t h
  have hp := ready_implies_pending sched j t h
  simp only [pending, Bool.and_eq_true] at hp
  exact hp.1

theorem jobs_must_arrive_to_be_ready {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [JobReady Job PState] :
    jobs_must_be_ready_to_execute sched → jobs_must_arrive_to_execute sched :=
  fun h j t hs => ready_implies_arrived sched j t (h j t hs)

theorem valid_schedule_implies_jobs_must_arrive_to_execute {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [JobReady Job PState] :
    ∀ arr_seq : arrival_sequence Job,
      valid_schedule sched arr_seq → jobs_must_arrive_to_execute sched :=
  fun _ h => jobs_must_arrive_to_be_ready sched h.2

theorem backlogged_implies_arrived {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [JobReady Job PState] :
    ∀ (j : Job) (t : instant), backlogged sched j t = true → has_arrived j t = true := by
  intro j t h
  simp only [backlogged, Bool.and_eq_true] at h
  exact ready_implies_arrived sched j t h.1

theorem backlogged_implies_incomplete {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [JobReady Job PState] :
    ∀ (j : Job) (t : instant), backlogged sched j t = true → (!completed_by sched j t) = true := by
  intro j t h
  simp only [backlogged, Bool.and_eq_true] at h
  have hp := any_ready_job_is_pending sched j t h.1
  simp only [pending, Bool.and_eq_true] at hp
  exact hp.2

theorem job_scheduled_implies_ready {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [JobReady Job PState] :
    jobs_must_be_ready_to_execute sched →
      ∀ (j : Job) (t : instant), scheduled_at sched j t = true → job_ready sched j t = true :=
  fun h => h

theorem valid_schedule_jobs_come_from_arrival_sequence {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [JobReady Job PState] :
    ∀ arr_seq : arrival_sequence Job,
      valid_schedule sched arr_seq → jobs_come_from_arrival_sequence sched arr_seq :=
  fun _ h => h.1

theorem valid_schedule_jobs_must_be_ready_to_execute {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (sched : schedule PState)
    [JobCost Job] [JobArrival Job] [JobReady Job PState] :
    ∀ arr_seq : arrival_sequence Job,
      valid_schedule sched arr_seq → jobs_must_be_ready_to_execute sched :=
  fun _ h => h.2

/-! ### Arrival-sequence prefixes -/

private theorem bigCat_split {α : Type _} (F : Nat → List α) (t1 t t2 : Nat)
    (h1 : t1 ≤ t) (h2 : t ≤ t2) :
    bigCat t1 t2 F = bigCat t1 t F ++ bigCat t t2 F := by
  unfold bigCat
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le h1
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h2
  have e1 : t1 + a + b - t1 = a + b := by nomega
  have e2 : t1 + a - t1 = a := by nomega
  have e3 : t1 + a + b - (t1 + a) = b := by nomega
  rw [e1, e2, e3, List.range_add, List.map_append, List.flatten_append]
  congr 2
  simp only [List.map_map]
  congr 1
  funext i
  simp [Function.comp, Nat.add_assoc]

private theorem mem_bigCat_iff {α : Type _} [DecidableEq α] (F : Nat → List α)
    (x : α) (m n : Nat) :
    x ∈ bigCat m n F ↔ ∃ i, x ∈ F i ∧ m ≤ i ∧ i < n := by
  constructor
  · exact mem_bigcat_nat_exists F x m n
  · rintro ⟨i, hx, hm, hn⟩
    exact mem_bigcat_nat F x m n i ⟨hm, hn⟩ hx

theorem arrivals_between_cat {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ t1 t t2 : Nat, t1 ≤ t → t ≤ t2 →
      arrivals_between arr_seq t1 t2 =
        arrivals_between arr_seq t1 t ++ arrivals_between arr_seq t t2 := by
  intro t1 t t2 h1 h2
  exact bigCat_split _ t1 t t2 h1 h2

theorem arrivals_P_cat {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ (P : Job → Bool) (t t1 t2 : Nat),
      (decide (t1 ≤ t) && decide (t < t2)) = true →
      arrivals_between_P arr_seq P t1 t2 =
        arrivals_between_P arr_seq P t1 t ++ arrivals_between_P arr_seq P t t2 := by
  intro P t t1 t2 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  unfold arrivals_between_P
  rw [arrivals_between_cat arr_seq t1 t t2 h.1 (Nat.le_of_lt h.2), List.filter_append]

theorem arrivals_between_mem_cat {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t1 t t2 : Nat), t1 ≤ t → t ≤ t2 →
      decide (j ∈ arrivals_between arr_seq t1 t2) =
        decide (j ∈ arrivals_between arr_seq t1 t ++ arrivals_between arr_seq t t2) := by
  intro j t1 t t2 h1 h2
  rw [arrivals_between_cat arr_seq t1 t t2 h1 h2]

theorem arrivals_between_sub {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t1 t1' t2 t2' : Nat), t1' ≤ t1 → t2 ≤ t2' →
      decide (j ∈ arrivals_between arr_seq t1 t2) = true →
      decide (j ∈ arrivals_between arr_seq t1' t2') = true := by
  intro j t1 t1' t2 t2' h1 h2 h
  obtain ⟨i, hi, hm, hn⟩ := (mem_bigCat_iff _ _ _ _).mp (of_decide_eq_true h)
  exact decide_eq_true ((mem_bigCat_iff _ _ _ _).mpr ⟨i, hi, by nomega, by nomega⟩)

theorem job_arrival_arrives_at {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t : instant), arrives_at arr_seq j t = true → job_arrival j = t :=
  fun h => h

theorem job_arrival_at {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t : instant),
        decide (j ∈ arrivals_at arr_seq t) = true → job_arrival j = t :=
  fun h j t hm => h j t hm

theorem job_in_arrivals_at {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t : instant), arrives_in arr_seq j → job_arrival j = t →
        decide (j ∈ arrivals_at arr_seq t) = true := by
  intro h j t ⟨t', ht'⟩ harr
  have := h j t' ht'
  subst harr
  rw [this]
  exact ht'

private theorem mem_arrivals_between_iff {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) (hc : consistent_arrival_times arr_seq)
    (j : Job) (t1 t2 : instant) :
    j ∈ arrivals_between arr_seq t1 t2 ↔
      arrives_in arr_seq j ∧ t1 ≤ job_arrival j ∧ job_arrival j < t2 := by
  unfold arrivals_between
  rw [mem_bigCat_iff]
  constructor
  · rintro ⟨i, hi, hm, hn⟩
    have hai : arrives_at arr_seq j i = true := by
      simpa [arrives_at] using hi
    have := hc j i hai
    exact ⟨⟨i, hai⟩, by nomega, by nomega⟩
  · rintro ⟨⟨t, ht⟩, hm, hn⟩
    have := hc j t ht
    refine ⟨t, ?_, by nomega, by nomega⟩
    simpa [arrives_at] using ht

theorem job_arrival_between {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t1 t2 : instant),
        decide (j ∈ arrivals_between arr_seq t1 t2) = true →
        (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true := by
  intro hc j t1 t2 h
  obtain ⟨_, hm, hn⟩ := (mem_arrivals_between_iff arr_seq hc j t1 t2).mp (of_decide_eq_true h)
  simp [hm, hn]

theorem job_arrival_between_ge {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t1 t2 : instant),
        decide (j ∈ arrivals_between arr_seq t1 t2) = true → t1 ≤ job_arrival j := by
  intro hc j t1 t2 h
  exact ((mem_arrivals_between_iff arr_seq hc j t1 t2).mp (of_decide_eq_true h)).2.1

theorem job_arrival_between_lt {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t1 t2 : instant),
        decide (j ∈ arrivals_between arr_seq t1 t2) = true → job_arrival j < t2 := by
  intro hc j t1 t2 h
  exact ((mem_arrivals_between_iff arr_seq hc j t1 t2).mp (of_decide_eq_true h)).2.2

theorem arrivals_between_filter_nil {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (t1 : Nat) (t2 : instant) (t : Nat), t < t1 →
        (arrivals_between arr_seq t1 t2).filter (fun j => decide (job_arrival j < t)) = [] := by
  intro hc t1 t2 t ht
  rw [List.filter_eq_nil_iff]
  intro j hj
  have := ((mem_arrivals_between_iff arr_seq hc j t1 t2).mp hj).2.1
  simp only [decide_eq_true_eq]
  nomega

theorem arrivals_between_filter {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (t1 : instant) (t2 t : Nat), t ≤ t2 →
        arrivals_between arr_seq t1 t =
          (arrivals_between arr_seq t1 t2).filter (fun j => decide (job_arrival j < t)) := by
  intro hc t1 t2 t ht
  by_cases h1 : t1 ≤ t
  · rw [arrivals_between_cat arr_seq t1 t t2 h1 ht, List.filter_append]
    have hleft : (arrivals_between arr_seq t1 t).filter (fun j => decide (job_arrival j < t)) =
        arrivals_between arr_seq t1 t := by
      rw [List.filter_eq_self]
      intro j hj
      have := ((mem_arrivals_between_iff arr_seq hc j t1 t).mp hj).2.2
      simpa using this
    have hright : (arrivals_between arr_seq t t2).filter (fun j => decide (job_arrival j < t)) =
        [] := by
      rw [List.filter_eq_nil_iff]
      intro j hj
      have := ((mem_arrivals_between_iff arr_seq hc j t t2).mp hj).2.1
      simp only [decide_eq_true_eq]
      nomega
    rw [hleft, hright, List.append_nil]
  · have hnil : arrivals_between arr_seq t1 t = [] := by
      unfold arrivals_between bigCat
      rw [show t - t1 = 0 by nomega]
      rfl
    rw [hnil, eq_comm, List.filter_eq_nil_iff]
    intro j hj
    have := ((mem_arrivals_between_iff arr_seq hc j t1 t2).mp hj).2.1
    simp only [decide_eq_true_eq]
    nomega

theorem in_arrivals_implies_arrived {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ (j : Job) (t1 t2 : instant),
      decide (j ∈ arrivals_between arr_seq t1 t2) = true → arrives_in arr_seq j := by
  intro j t1 t2 h
  obtain ⟨i, hi, _, _⟩ := (mem_bigCat_iff _ _ _ _).mp (of_decide_eq_true h)
  exact ⟨i, by simpa [arrives_at] using hi⟩

theorem in_arrseq_implies_arrives {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ (t : instant) (j : Job), decide (j ∈ arr_seq t) = true → arrives_in arr_seq j :=
  fun t _ h => ⟨t, h⟩

theorem in_arrivals_implies_arrived_between {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t1 t2 : instant),
        decide (j ∈ arrivals_between arr_seq t1 t2) = true → arrived_between j t1 t2 = true :=
  job_arrival_between arr_seq

theorem in_arrivals_implies_arrived_before {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t : instant),
        decide (j ∈ arrivals_before arr_seq t) = true → arrived_before j t = true := by
  intro hc j t h
  simp only [arrived_before, decide_eq_true_eq]
  exact job_arrival_between_lt arr_seq hc j 0 t h

theorem arrived_between_implies_in_arrivals {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t1 t2 : instant), arrives_in arr_seq j →
        arrived_between j t1 t2 = true →
        decide (j ∈ arrivals_between arr_seq t1 t2) = true := by
  intro hc j t1 t2 ha hb
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at hb
  exact decide_eq_true ((mem_arrivals_between_iff arr_seq hc j t1 t2).mpr ⟨ha, hb.1, hb.2⟩)

theorem job_arrival_between_P {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (P : Job → Bool) (t1 t2 : instant),
        decide (j ∈ arrivals_between_P arr_seq P t1 t2) = true →
        (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true := by
  intro hc j P t1 t2 h
  have h' := (List.mem_filter.mp (of_decide_eq_true h)).1
  exact job_arrival_between arr_seq hc j t1 t2 (decide_eq_true h')

theorem job_in_arrivals_between {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t1 t2 : Nat), arrives_in arr_seq j → t1 ≤ job_arrival j →
        job_arrival j < t2 → decide (j ∈ arrivals_between arr_seq t1 t2) = true := by
  intro hc j t1 t2 ha h1 h2
  exact decide_eq_true ((mem_arrivals_between_iff arr_seq hc j t1 t2).mpr ⟨ha, h1, h2⟩)

theorem arrivals_uniq {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq → arrival_sequence_uniq arr_seq →
      ∀ t1 t2 : instant, (arrivals_between arr_seq t1 t2).Nodup := by
  intro hc hu t1 t2
  apply bigcat_nat_uniq
  · exact hu
  · intro x i1 i2 h1 h2
    have e1 := hc x i1 (by simpa [arrives_at] using h1)
    have e2 := hc x i2 (by simpa [arrives_at] using h2)
    nomega

theorem arrivals_between_geq {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ t1 t2 : Nat, t2 ≤ t1 → arrivals_between arr_seq t1 t2 = [] := by
  intro t1 t2 h
  unfold arrivals_between bigCat
  rw [show t2 - t1 = 0 by nomega]
  rfl

theorem arrivals_between_nonempty {Job : JobType} [DecidableEq Job]
    (arr_seq : arrival_sequence Job) :
    ∀ (t1 t2 : instant) (j : Job),
      decide (j ∈ arrivals_between arr_seq t1 t2) = true → t1 < t2 := by
  intro t1 t2 j h
  obtain ⟨i, _, hm, hn⟩ := (mem_bigCat_iff _ _ _ _).mp (of_decide_eq_true h)
  nomega

theorem arrival_lt_implies_job_in_arrivals_between_P {Job : JobType} [DecidableEq Job]
    [JobArrival Job] (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j1 j2 : Job) (P : Job → Bool) (t1 t2 : instant),
        decide (j1 ∈ arrivals_between_P arr_seq P t1 t2) = true →
        decide (j2 ∈ arrivals_between_P arr_seq P t1 t2) = true →
        job_arrival j2 < job_arrival j1 →
        decide (j2 ∈ arrivals_between_P arr_seq P t1 (job_arrival j1)) = true := by
  intro hc j1 j2 P t1 t2 h1 h2 hlt
  have m1 := List.mem_filter.mp (of_decide_eq_true h1)
  have m2 := List.mem_filter.mp (of_decide_eq_true h2)
  have b1 := (mem_arrivals_between_iff arr_seq hc j1 t1 t2).mp m1.1
  have b2 := (mem_arrivals_between_iff arr_seq hc j2 t1 t2).mp m2.1
  refine decide_eq_true (List.mem_filter.mpr ⟨?_, m2.2⟩)
  exact (mem_arrivals_between_iff arr_seq hc j2 t1 (job_arrival j1)).mpr ⟨b2.1, b2.2.1, hlt⟩

theorem job_arrival_in_bounds {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t1 t2 : instant),
        decide (j ∈ arrivals_between arr_seq t1 t2) = true ↔
          arrives_in arr_seq j ∧
            (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true := by
  intro hc j t1 t2
  rw [decide_eq_true_iff, mem_arrivals_between_iff arr_seq hc]
  simp

/-- Order jobs by non-decreasing arrival time. -/
def by_arrival_times {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (j1 j2 : Job) : Bool :=
  decide (job_arrival j1 ≤ job_arrival j2)

private theorem pairwise_of_same_arrival {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (t : instant) :
    ∀ l : List Job, (∀ j ∈ l, job_arrival j = t) →
      List.Pairwise (fun a b => by_arrival_times a b = true) l
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
      refine List.Pairwise.cons ?_ (pairwise_of_same_arrival t l
        (fun j hj => h j (List.mem_cons_of_mem _ hj)))
      intro b hb
      simp [by_arrival_times, h a (List.mem_cons_self), h b (List.mem_cons_of_mem _ hb)]

theorem arrivals_at_sorted {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ t : instant,
        List.IsChain (fun a b => by_arrival_times a b = true) (arrivals_at arr_seq t) := by
  intro hc t
  apply List.Pairwise.isChain
  exact pairwise_of_same_arrival t _ (fun j hj => hc j t (by simpa [arrives_at] using hj))

theorem arrivals_between_sorted {Job : JobType} [DecidableEq Job] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ t1 t2 : instant,
        List.IsChain (fun a b => by_arrival_times a b = true) (arrivals_between arr_seq t1 t2) := by
  intro hc t1 t2
  apply List.Pairwise.isChain
  have hblock : ∀ s j, j ∈ arrivals_at arr_seq s → job_arrival j = s :=
    fun s j hj => hc j s (by simpa [arrives_at] using hj)
  unfold arrivals_between bigCat
  rw [List.pairwise_flatten]
  constructor
  · intro l hl
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
    exact pairwise_of_same_arrival (t1 + i) _ (hblock (t1 + i))
  · rw [List.pairwise_map]
    refine (List.pairwise_lt_range (n := t2 - t1)).imp ?_
    intro i k hik x hx y hy
    simp [by_arrival_times, hblock _ x hx, hblock _ y hy]
    nomega

theorem arrivals_between_partitioned_by_task {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
      ∀ (t1 t2 : instant) (j : Job),
        decide (j ∈ arrivals_between arr_seq t1 t2) =
          decide (j ∈ bigCatSeqAll ts (fun tsk => task_arrivals_between arr_seq tsk t1 t2)) := by
  intro ts hts t1 t2 j
  have h := bigcat_partitions (arrivals_between arr_seq t1 t2) ts (fun _ => true)
    (fun x => job_task (Task := Task) x)
    (fun x hx _ => of_decide_eq_true
      (hts x (in_arrivals_implies_arrived arr_seq x t1 t2 (decide_eq_true hx)))) j
  simp only [List.filter_true, Bool.true_and] at h
  rw [h]
  rfl

/-! ### Scheduled jobs have arrived -/

theorem arrives_in_jobs_come_from_arrival_sequence {Job : JobType} [DecidableEq Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState) :
    jobs_come_from_arrival_sequence sched arr_seq →
      ∀ (j : Job) (t : instant), scheduled_at sched j t = true → arrives_in arr_seq j :=
  fun h => h

theorem arrived_between_jobs_must_arrive_to_execute {Job : JobType} [DecidableEq Job]
    [JobArrival Job] {PState : ProcessorState Job} (sched : schedule PState) :
    jobs_must_arrive_to_execute sched →
      ∀ (j : Job) (t : instant), scheduled_at sched j t = true → has_arrived j t = true :=
  fun h => h

theorem arrivals_before_scheduled_at {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ (j : Job) (t : instant), scheduled_at sched j t = true →
          ∀ t' : Nat, t < t' → decide (j ∈ arrivals_before arr_seq t') = true := by
  intro hc sched hfrom hmust j t hs t' ht
  have ha := hfrom j t hs
  have hle : job_arrival j ≤ t := of_decide_eq_true (hmust j t hs)
  exact job_in_arrivals_between arr_seq hc j 0 t' ha (Nat.zero_le _) (Nat.lt_of_le_of_lt hle ht)

theorem arrivals_up_to_scheduled_at {Job : JobType} [DecidableEq Job] [JobArrival Job]
    {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ sched : schedule PState,
        jobs_come_from_arrival_sequence sched arr_seq → jobs_must_arrive_to_execute sched →
        ∀ (j : Job) (t : instant), scheduled_at sched j t = true →
          ∀ t' : Nat, t ≤ t' → decide (j ∈ arrivals_up_to arr_seq t') = true := by
  intro hc sched hfrom hmust j t hs t' ht
  have ha := hfrom j t hs
  have hle : job_arrival j ≤ t := of_decide_eq_true (hmust j t hs)
  exact job_in_arrivals_between arr_seq hc j 0 (t' + 1) ha (Nat.zero_le _)
    (Nat.lt_succ_of_le (Nat.le_trans hle ht))

end Prosa.Analysis.Facts.Behavior.Arrivals
