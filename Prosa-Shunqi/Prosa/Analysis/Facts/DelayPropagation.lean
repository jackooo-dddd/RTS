-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/delay_propagation.v

import Prosa.Analysis.Definitions.DelayPropagation
import Prosa.Analysis.Facts.Behavior.Arrivals

namespace Prosa.Analysis.Facts.DelayPropagation

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Analysis.Definitions.DelayPropagation
open Prosa.Analysis.Facts.Behavior.Arrivals

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

/-! Representation notes: `x \in s` in Prop position is `decide (x ∈ s) = true`;
`{subset xs <= ys}` is `∀ x, decide (x ∈ xs) = true → decide (x ∈ ys) = true`;
`{in xs &, injective f}` is
`∀ x y, decide (x ∈ xs) = true → decide (y ∈ xs) = true → f x = f y → x = y`;
`uniq s` is `s.Nodup`; `[seq f x | x <- s]` is `s.map f`; `a <= b < c` is
`(decide (a ≤ b) && decide (b < c)) = true`. -/

/-! ## Source-local instances

`LEAN_HELPER`s for the source's `#[local]` instances (not in the public
inventory): `propagated_arrival_curve` of `analysis/definitions/delay_propagation.v`
and `max_arrivals2` of this file.  The source's `if delta is 0 then 0 else …`
is the same two-case match. -/

@[instance_reducible] def propagated_arrival_curve {Task1 Task2 : TaskType}
    [DecidableEq Task1] [DecidableEq Task2] (task1_of : Task2 → Task1)
    (delay_bound : Task2 → duration) [MaxArrivals Task1] : MaxArrivals Task2 where
  max_arrivals tsk2 delta :=
    match delta with
    | 0 => 0
    | _ + 1 => max_arrivals (task1_of tsk2) (delta + delay_bound tsk2)

@[instance_reducible] def max_arrivals2 {Task1 Task2 : TaskType}
    [DecidableEq Task1] [DecidableEq Task2] (task1_of : Task2 → Task1)
    (delay_bound : Task2 → duration) [MaxArrivals Task1] : MaxArrivals Task2 :=
  propagated_arrival_curve task1_of delay_bound

section ArrivalSequence

variable {Task2 : TaskType} [DecidableEq Task2]
variable {Job1 Job2 : JobType} [DecidableEq Job1] [DecidableEq Job2] [JobTask Job2 Task2]

private theorem mem_propagated [JA1 : JobArrival Job1] (job1_of : Job2 → Job1)
    (arr_seq1 : arrival_sequence Job1) (job2_of : Job1 → List Job2)
    (arrival_delay : Job2 → duration) (t : instant) (j2 : Job2) :
    j2 ∈ propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay t ↔
      (∃ j1, j1 ∈ arrivals_up_to arr_seq1 t ∧ j2 ∈ job2_of j1) ∧
        JA1.job_arrival (job1_of j2) + arrival_delay j2 = t := by
  unfold propagated_arrival_sequence
  simp only [List.mem_filter, List.mem_flatten, List.mem_map, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨l, ⟨j1, hj1, hjl⟩, hl⟩, h⟩
    subst hjl
    exact ⟨⟨j1, hj1, hl⟩, h⟩
  · rintro ⟨⟨j1, hj1, hl⟩, h⟩
    exact ⟨⟨_, ⟨j1, hj1, rfl⟩, hl⟩, h⟩

theorem consistent_propagated_arrival_sequence [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (job2_of : Job1 → List Job2) (arrival_delay : Job2 → duration)
    (delay_bound : Task2 → duration) (ts2 : List Task2) (arr_seq1 : arrival_sequence Job1) :
    valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
      consistent_arrival_times
        (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) := by
  intro hmap j2 t h
  have hm := (mem_propagated job1_of arr_seq1 job2_of arrival_delay t j2).mp
    (of_decide_eq_true h)
  rw [hmap.2.2.2 j2]
  exact hm.2

theorem propagated_arrival_sequence_uniq [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (job2_of : Job1 → List Job2) (arrival_delay : Job2 → duration)
    (delay_bound : Task2 → duration) (ts2 : List Task2) (arr_seq1 : arrival_sequence Job1) :
    valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
      valid_arrival_sequence arr_seq1 →
      arrival_sequence_uniq
        (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) := by
  intro hmap hva t
  unfold arrivals_at propagated_arrival_sequence
  apply List.Nodup.filter
  have hnd := arrivals_uniq arr_seq1 hva.1 hva.2 0 (t + 1)
  rw [List.nodup_flatten]
  refine ⟨?_, ?_⟩
  · intro l hl
    obtain ⟨j1, hj1, rfl⟩ := List.mem_map.mp hl
    exact hmap.2.1 j1 (in_arrivals_implies_arrived arr_seq1 j1 0 (t + 1) (decide_eq_true hj1))
  · refine List.Pairwise.map _ (fun a b hab => ?_) hnd
    intro x hxa hxb
    have ha' : job1_of x = a := (hmap.1 a x).mp (decide_eq_true hxa)
    have hb' : job1_of x = b := (hmap.1 b x).mp (decide_eq_true hxb)
    exact hab (ha'.symm.trans hb')

theorem valid_propagated_arrival_sequence [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (job2_of : Job1 → List Job2) (arrival_delay : Job2 → duration)
    (delay_bound : Task2 → duration) (ts2 : List Task2) (arr_seq1 : arrival_sequence Job1) :
    valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
      valid_arrival_sequence arr_seq1 →
      valid_arrival_sequence
        (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) :=
  fun hmap hva =>
    ⟨consistent_propagated_arrival_sequence job1_of job2_of arrival_delay delay_bound ts2 arr_seq1 hmap,
      propagated_arrival_sequence_uniq job1_of job2_of arrival_delay delay_bound ts2 arr_seq1 hmap hva⟩

theorem arrives_in_propagated_if [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (job2_of : Job1 → List Job2) (arrival_delay : Job2 → duration)
    (delay_bound : Task2 → duration) (ts2 : List Task2) (arr_seq1 : arrival_sequence Job1) :
    valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
      ∀ j2 : Job2, consistent_arrival_times arr_seq1 → arrives_in arr_seq1 (job1_of j2) →
        arrives_in (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) j2 := by
  intro hmap j2 hc hin
  obtain ⟨t, ht⟩ := hin
  have hta : JA1.job_arrival (job1_of j2) = t := hc _ t ht
  refine ⟨t + arrival_delay j2, decide_eq_true ?_⟩
  unfold arrivals_at
  refine (mem_propagated job1_of arr_seq1 job2_of arrival_delay _ j2).mpr ⟨⟨job1_of j2, ?_, ?_⟩, by omega'⟩
  · exact of_decide_eq_true (job_in_arrivals_between arr_seq1 hc (job1_of j2) 0 _ ⟨t, ht⟩
      (Nat.zero_le _) (by omega'))
  · exact of_decide_eq_true ((hmap.1 (job1_of j2) j2).mpr rfl)

theorem arrives_in_propagated_only_if [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (job2_of : Job1 → List Job2) (arrival_delay : Job2 → duration)
    (delay_bound : Task2 → duration) (ts2 : List Task2) (arr_seq1 : arrival_sequence Job1) :
    valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
      ∀ j2 : Job2,
        arrives_in (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) j2 →
        arrives_in arr_seq1 (job1_of j2) := by
  intro hmap j2 hin
  obtain ⟨t, ht⟩ := hin
  have hm := (mem_propagated job1_of arr_seq1 job2_of arrival_delay t j2).mp (of_decide_eq_true ht)
  obtain ⟨⟨j1, hj1, hj2⟩, _⟩ := hm
  have heq : job1_of j2 = j1 := by simpa using (hmap.1 j1 j2).mp (decide_eq_true hj2)
  rw [heq]
  exact in_arrivals_implies_arrived arr_seq1 j1 0 (t + 1) (decide_eq_true hj1)

end ArrivalSequence

/-! ## Correctness of the propagated arrival curve -/

theorem propagated_arrival_curve_valid {Task1 Task2 : TaskType} [DecidableEq Task1]
    [DecidableEq Task2] (task1_of : Task2 → Task1) (delay_bound : Task2 → duration)
    (ts2 : List Task2) [max_arrivals1 : MaxArrivals Task1] :
    (∀ tsk2 : Task2, decide (tsk2 ∈ ts2) = true →
        Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) (max_arrivals (task1_of tsk2))) →
      valid_taskset_arrival_curve ts2
        (@MaxArrivals.max_arrivals Task2 _ (max_arrivals2 task1_of delay_bound)) := by
  intro hmono tsk2 hin
  refine ⟨rfl, ?_⟩
  intro x y hxy
  have hle := of_decide_eq_true hxy
  apply decide_eq_true
  cases x with
  | zero => exact Nat.zero_le _
  | succ x =>
    cases y with
    | zero => exact absurd hle (by simp)
    | succ y =>
      show max_arrivals (task1_of tsk2) (x + 1 + delay_bound tsk2) ≤
        max_arrivals (task1_of tsk2) (y + 1 + delay_bound tsk2)
      exact of_decide_eq_true (hmono tsk2 hin _ _ (decide_eq_true (by omega')))

section CorrectnessSteps

variable {Task2 : TaskType} [DecidableEq Task2]
variable {Job1 Job2 : JobType} [DecidableEq Job1] [DecidableEq Job2] [JobTask Job2 Task2]

theorem trigger_job_arrival_bounded [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (job2_of : Job1 → List Job2) (arrival_delay : Job2 → duration)
    (delay_bound : Task2 → duration) (ts2 : List Task2) (arr_seq1 : arrival_sequence Job1) :
    valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
      ∀ t1 t2 : instant, t1 ≤ t2 → ∀ tsk2 : Task2, decide (tsk2 ∈ ts2) = true →
        ∀ j1 : Job1,
          decide (j1 ∈ (task_arrivals_between
              (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) tsk2 t1 t2).map
              job1_of) = true →
          (decide (t1 - delay_bound tsk2 ≤ job_arrival j1) && decide (job_arrival j1 < t2)) = true := by
  intro hmap t1 t2 _ tsk2 hin2 j1 hj1
  obtain ⟨j2, hj2, rfl⟩ := List.mem_map.mp (of_decide_eq_true hj1)
  have hf := List.mem_filter.mp hj2
  have htsk : job_task j2 = tsk2 := by simpa [job_of_task] using hf.2
  have hc2 := consistent_propagated_arrival_sequence job1_of job2_of arrival_delay delay_bound ts2
    arr_seq1 hmap
  have hb := job_arrival_between _ hc2 j2 t1 t2 (decide_eq_true hf.1)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
  have hdef := hmap.2.2.2 j2
  have harr2 := in_arrivals_implies_arrived _ j2 t1 t2 (decide_eq_true hf.1)
  have harr1 := arrives_in_propagated_only_if job1_of job2_of arrival_delay delay_bound ts2 arr_seq1
    hmap j2 harr2
  have hbound := hmap.2.2.1 j2 (by rw [htsk]; exact hin2) harr1
  rw [htsk] at hbound
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor <;> omega'

end CorrectnessSteps

section CorrectnessSteps2

variable {Task1 Task2 : TaskType} [DecidableEq Task1] [DecidableEq Task2]
variable {Job1 Job2 : JobType} [DecidableEq Job1] [DecidableEq Job2]
variable [JobTask Job1 Task1] [JobTask Job2 Task2]

theorem subset_trigger_jobs [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (task1_of : Task2 → Task1) (job2_of : Job1 → List Job2)
    (arrival_delay : Job2 → duration) (delay_bound : Task2 → duration) (ts2 : List Task2) :
    valid_delay_propagation_mapping JA1 JA2 job1_of task1_of delay_bound ts2 →
      ∀ arr_seq1 : arrival_sequence Job1,
        valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
        valid_arrival_sequence arr_seq1 →
        ∀ t1 t2 : instant, t1 ≤ t2 → ∀ tsk2 : Task2, decide (tsk2 ∈ ts2) = true →
          ∀ j1 : Job1,
            decide (j1 ∈ (task_arrivals_between
                (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) tsk2 t1 t2).map
                job1_of) = true →
            decide (j1 ∈ task_arrivals_between arr_seq1 (task1_of tsk2) (t1 - delay_bound tsk2) t2) = true := by
  intro hvm arr_seq1 hmap hva t1 t2 hle tsk2 hin2 j1 hj1
  have hbd := trigger_job_arrival_bounded job1_of job2_of arrival_delay delay_bound ts2 arr_seq1 hmap
    t1 t2 hle tsk2 hin2 j1 hj1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbd
  obtain ⟨j2, hj2, rfl⟩ := List.mem_map.mp (of_decide_eq_true hj1)
  have hf := List.mem_filter.mp hj2
  have htsk : job_task j2 = tsk2 := by simpa [job_of_task] using hf.2
  have harr1 := arrives_in_propagated_only_if job1_of job2_of arrival_delay delay_bound ts2 arr_seq1
    hmap j2 (in_arrivals_implies_arrived _ j2 t1 t2 (decide_eq_true hf.1))
  apply decide_eq_true
  refine List.mem_filter.mpr ⟨?_, ?_⟩
  · exact of_decide_eq_true (job_in_arrivals_between arr_seq1 hva.1 _ _ _ harr1 hbd.1 hbd.2)
  · simp only [job_of_task, decide_eq_true_eq]
    rw [hvm.1 j2, htsk]

theorem job1_of_inj [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (task1_of : Task2 → Task1) (job2_of : Job1 → List Job2)
    (arrival_delay : Job2 → duration) (delay_bound : Task2 → duration) (ts2 : List Task2) :
    valid_delay_propagation_mapping JA1 JA2 job1_of task1_of delay_bound ts2 →
      ∀ arr_seq1 : arrival_sequence Job1,
        valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
        (∀ tsk1 : Task1, decide (tsk1 ∈ ts2.map task1_of) = true →
          ∀ j1 : Job1, job_task j1 = tsk1 → (job2_of j1).length ≤ 1) →
        ∀ (t1 t2 : instant) (tsk2 : Task2), decide (tsk2 ∈ ts2) = true →
          ∀ x y : Job2,
            decide (x ∈ task_arrivals_between
              (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) tsk2 t1 t2) = true →
            decide (y ∈ task_arrivals_between
              (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) tsk2 t1 t2) = true →
            job1_of x = job1_of y → x = y := by
  intro hvm arr_seq1 hmap hsing t1 t2 tsk2 _ x y _ hy heq
  have hfy := List.mem_filter.mp (of_decide_eq_true hy)
  have htsky : job_task y = tsk2 := by simpa [job_of_task] using hfy.2
  have hsize : (job2_of (job1_of y)).length ≤ 1 :=
    hsing (task1_of (job_task y)) (decide_eq_true (List.mem_map.mpr ⟨job_task y, by
      rw [htsky]; exact of_decide_eq_true (by assumption), rfl⟩)) _ (hvm.1 y)
  have hxm : x ∈ job2_of (job1_of y) := by
    rw [← heq]; exact of_decide_eq_true ((hmap.1 (job1_of x) x).mpr rfl)
  have hym : y ∈ job2_of (job1_of y) := of_decide_eq_true ((hmap.1 (job1_of y) y).mpr rfl)
  match hl : job2_of (job1_of y), hsize with
  | [], _ => rw [hl] at hym; simp at hym
  | [z], _ =>
      rw [hl] at hxm hym
      simp at hxm hym
      rw [hxm, hym]
  | _ :: _ :: _, h => simp at h

theorem uniq_trigger_jobs [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (task1_of : Task2 → Task1) (job2_of : Job1 → List Job2)
    (arrival_delay : Job2 → duration) (delay_bound : Task2 → duration) (ts2 : List Task2) :
    valid_delay_propagation_mapping JA1 JA2 job1_of task1_of delay_bound ts2 →
      ∀ arr_seq1 : arrival_sequence Job1,
        valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
        (∀ tsk1 : Task1, decide (tsk1 ∈ ts2.map task1_of) = true →
          ∀ j1 : Job1, job_task j1 = tsk1 → (job2_of j1).length ≤ 1) →
        valid_arrival_sequence arr_seq1 →
        ∀ (t1 t2 : instant) (tsk2 : Task2), decide (tsk2 ∈ ts2) = true →
          ((task_arrivals_between
              (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) tsk2 t1 t2).map
              job1_of).Nodup := by
  intro hvm arr_seq1 hmap hsing hva t1 t2 tsk2 hin2
  have hva2 := valid_propagated_arrival_sequence job1_of job2_of arrival_delay delay_bound ts2
    arr_seq1 hmap hva
  apply List.Nodup.map_on
  · intro x hx y hy heq
    exact job1_of_inj job1_of task1_of job2_of arrival_delay delay_bound ts2 hvm arr_seq1 hmap hsing
      t1 t2 tsk2 hin2 x y (decide_eq_true hx) (decide_eq_true hy) heq
  · exact List.Nodup.filter _ (arrivals_uniq _ hva2.1 hva2.2 t1 t2)

theorem trigger_job_size [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (task1_of : Task2 → Task1) (job2_of : Job1 → List Job2)
    (arrival_delay : Job2 → duration) (delay_bound : Task2 → duration) (ts2 : List Task2) :
    valid_delay_propagation_mapping JA1 JA2 job1_of task1_of delay_bound ts2 →
      ∀ arr_seq1 : arrival_sequence Job1,
        valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
        (∀ tsk1 : Task1, decide (tsk1 ∈ ts2.map task1_of) = true →
          ∀ j1 : Job1, job_task j1 = tsk1 → (job2_of j1).length ≤ 1) →
        valid_arrival_sequence arr_seq1 →
        ∀ t1 t2 : instant, t1 ≤ t2 → ∀ tsk2 : Task2, decide (tsk2 ∈ ts2) = true →
          ((task_arrivals_between
              (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) tsk2 t1 t2).map
              job1_of).length ≤
            (task_arrivals_between arr_seq1 (task1_of tsk2) (t1 - delay_bound tsk2) t2).length := by
  intro hvm arr_seq1 hmap hsing hva t1 t2 hle tsk2 hin2
  apply List.Subperm.length_le
  apply List.subperm_of_subset
    (uniq_trigger_jobs job1_of task1_of job2_of arrival_delay delay_bound ts2 hvm arr_seq1 hmap hsing
      hva t1 t2 tsk2 hin2)
  intro j1 hj1
  exact of_decide_eq_true (subset_trigger_jobs job1_of task1_of job2_of arrival_delay delay_bound ts2
    hvm arr_seq1 hmap hva t1 t2 hle tsk2 hin2 j1 (decide_eq_true hj1))

theorem propagated_arrival_curve_respected [JA1 : JobArrival Job1] [JA2 : JobArrival Job2]
    (job1_of : Job2 → Job1) (task1_of : Task2 → Task1) (job2_of : Job1 → List Job2)
    (arrival_delay : Job2 → duration) (delay_bound : Task2 → duration) (ts2 : List Task2) :
    valid_delay_propagation_mapping JA1 JA2 job1_of task1_of delay_bound ts2 →
      ∀ (max_arrivals1 : MaxArrivals Task1) (arr_seq1 : arrival_sequence Job1),
        valid_arr_seq_propagation_mapping JA1 JA2 job1_of delay_bound arr_seq1 job2_of arrival_delay ts2 →
        (∀ tsk1 : Task1, decide (tsk1 ∈ ts2.map task1_of) = true →
          ∀ j1 : Job1, job_task j1 = tsk1 → (job2_of j1).length ≤ 1) →
        valid_arrival_sequence arr_seq1 →
        valid_taskset_arrival_curve (ts2.map task1_of) (@MaxArrivals.max_arrivals Task1 _ max_arrivals1) →
        @taskset_respects_max_arrivals Task1 _ Job1 _ _ arr_seq1 max_arrivals1 (ts2.map task1_of) →
        @taskset_respects_max_arrivals Task2 _ Job2 _ _
          (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay)
          (@max_arrivals2 Task1 Task2 _ _ task1_of delay_bound max_arrivals1) ts2 := by
  intro hvm max_arrivals1 arr_seq1 hmap hsing hva hvac hresp tsk2 hin2 t1 t2 hle
  have hin1 : decide (task1_of tsk2 ∈ ts2.map task1_of) = true :=
    decide_eq_true (List.mem_map.mpr ⟨tsk2, of_decide_eq_true hin2, rfl⟩)
  have hsize := trigger_job_size job1_of task1_of job2_of arrival_delay delay_bound ts2 hvm arr_seq1
    hmap hsing hva t1 t2 hle tsk2 hin2
  rw [List.length_map] at hsize
  rcases Nat.eq_zero_or_pos (t2 - t1) with hd | hd
  · have ht : t2 ≤ t1 := by omega'
    have h0 : number_of_task_arrivals
        (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) tsk2 t1 t2 = 0 := by
      unfold number_of_task_arrivals task_arrivals_between
      have hnil := arrivals_between_geq
        (propagated_arrival_sequence JA1 job1_of arr_seq1 job2_of arrival_delay) t1 t2 ht
      rw [hnil]
      rfl
    rw [h0]
    exact Nat.zero_le _
  · obtain ⟨d, hd'⟩ : ∃ d, t2 - t1 = d + 1 := ⟨t2 - t1 - 1, by omega'⟩
    rw [hd']
    show number_of_task_arrivals _ tsk2 t1 t2 ≤
      @MaxArrivals.max_arrivals Task1 _ max_arrivals1 (task1_of tsk2) (d + 1 + delay_bound tsk2)
    have hr := hresp (task1_of tsk2) hin1 (t1 - delay_bound tsk2) t2 (by omega')
    have hmono := (hvac (task1_of tsk2) hin1).2 (t2 - (t1 - delay_bound tsk2)) (d + 1 + delay_bound tsk2)
      (decide_eq_true (by omega'))
    have hm := of_decide_eq_true hmono
    unfold number_of_task_arrivals at hr ⊢
    omega'

end CorrectnessSteps2

end Prosa.Analysis.Facts.DelayPropagation
