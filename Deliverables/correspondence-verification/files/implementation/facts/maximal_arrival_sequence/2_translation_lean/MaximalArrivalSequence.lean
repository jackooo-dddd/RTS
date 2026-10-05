-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/facts/maximal_arrival_sequence.v

import Prosa.Analysis.Facts.Model.TaskArrivals
import Prosa.Implementation.Definitions.MaximalArrivalSequence

namespace Prosa.Implementation.Facts.MaximalArrivalSequence

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Util.Notation
open Prosa.Util.Bigcat
open Prosa.Util.Sum
open Prosa.Util.Supremum
open Prosa.Analysis.Facts.Model.TaskArrivals
open Prosa.Implementation.Definitions.MaximalArrivalSequence

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

/-! Representation notes: `uniq s` is `s.Nodup`; `x \in s` is
`decide (x ∈ s) = true`; `size` is `List.length`; `nth 0 s i` is
`s.getD i 0`; `iter t f [::]` is `Nat.repeat f t []` (as in the accepted
definitions); `\sum_(a <= i < b) F i` is `sumSeq (List.range' a (b - a)) F`;
`t <= h1 <= h2` is `(decide (t ≤ h1) && decide (h1 ≤ h2)) = true`;
`t.-1` is `t - 1` and `Δ.+1` is `Δ + 1`. -/

private theorem sumSeq_append {I : Type _} (a b : List I) (F : I → Nat) :
    sumSeq (a ++ b) F = sumSeq a F + sumSeq b F := by
  simp [sumSeq, List.map_append, List.sum_append]

private theorem sumSeq_congr_mem {I : Type _} (r : List I) (F G : I → Nat)
    (h : ∀ i, i ∈ r → F i = G i) : sumSeq r F = sumSeq r G := by
  unfold sumSeq
  rw [List.map_congr_left h]

private theorem mem_concrete {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] [MaxArrivals Task] (gen : Task → Nat → instant → List Job)
    (ts : List Task) (j : Job) (t : instant) :
    arrives_at (concrete_arrival_sequence gen ts) j t = true →
      ∃ tsk, tsk ∈ ts ∧ j ∈ gen tsk (max_arrivals_at tsk t) t := by
  intro h
  simp only [arrives_at, arrivals_at, decide_eq_true_eq, concrete_arrival_sequence,
    bigCatSeqAll, List.mem_flatMap] at h
  exact h

theorem arr_seq_is_a_set {Task : TaskType} [DecidableEq Task] {Job : JobType}
    [DecidableEq Job] (ts : List Task) [MaxArrivals Task]
    (generate_jobs_at : Task → Nat → instant → List Job) :
    (∀ t1 t2 : instant,
      (arrivals_between (concrete_arrival_sequence generate_jobs_at ts) t1 t2).Nodup) →
      arrival_sequence_uniq (concrete_arrival_sequence generate_jobs_at ts) := by
  intro h t
  have ht := h t (t + 1)
  simpa [arrivals_between, bigCat] using ht

theorem concrete_all_jobs_from_taskset {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (ts : List Task) [MaxArrivals Task]
    (generate_jobs_at : Task → Nat → instant → List Job) :
    (∀ (tsk : Task) (n : Nat) (t : instant) (j : Job),
      decide (j ∈ generate_jobs_at tsk n t) = true →
        job_task j = tsk ∧ job_arrival j = t ∧ job_cost j ≤ task_cost tsk) →
      all_jobs_from_taskset (concrete_arrival_sequence generate_jobs_at ts) ts := by
  intro hgen j ⟨t, ht⟩
  obtain ⟨tsk, htsk, hj⟩ := mem_concrete generate_jobs_at ts j t ht
  have := (hgen tsk _ t j (decide_eq_true hj)).1
  rw [this]
  exact decide_eq_true htsk

theorem arrival_times_are_consistent {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (ts : List Task) [MaxArrivals Task]
    (generate_jobs_at : Task → Nat → instant → List Job) :
    (∀ (tsk : Task) (n : Nat) (t : instant) (j : Job),
      decide (j ∈ generate_jobs_at tsk n t) = true →
        job_task j = tsk ∧ job_arrival j = t ∧ job_cost j ≤ task_cost tsk) →
      consistent_arrival_times (concrete_arrival_sequence generate_jobs_at ts) := by
  intro hgen j t ht
  obtain ⟨tsk, _, hj⟩ := mem_concrete generate_jobs_at ts j t ht
  exact (hgen tsk _ t j (decide_eq_true hj)).2.1

theorem concrete_valid_job_cost {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (ts : List Task) [MaxArrivals Task]
    (generate_jobs_at : Task → Nat → instant → List Job) :
    (∀ (tsk : Task) (n : Nat) (t : instant) (j : Job),
      decide (j ∈ generate_jobs_at tsk n t) = true →
        job_task j = tsk ∧ job_arrival j = t ∧ job_cost j ≤ task_cost tsk) →
      arrivals_have_valid_job_costs (Task := Task)
        (concrete_arrival_sequence generate_jobs_at ts) := by
  intro hgen j ⟨t, ht⟩
  obtain ⟨tsk, _, hj⟩ := mem_concrete generate_jobs_at ts j t ht
  obtain ⟨htask, _, hcost⟩ := hgen tsk _ t j (decide_eq_true hj)
  unfold valid_job_cost
  rw [htask]
  exact decide_eq_true hcost

theorem task_arrivals_at_eq_generate_jobs_at {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] (ts : List Task) (h_uniq : ts.Nodup) [MaxArrivals Task]
    (generate_jobs_at : Task → Nat → instant → List Job) :
    (∀ (tsk : Task) (n : Nat) (t : instant) (j : Job),
      decide (j ∈ generate_jobs_at tsk n t) = true →
        job_task j = tsk ∧ job_arrival j = t ∧ job_cost j ≤ task_cost tsk) →
      ∀ tsk : Task, decide (tsk ∈ ts) = true → ∀ t : instant,
        task_arrivals_at (concrete_arrival_sequence generate_jobs_at ts) tsk t =
          generate_jobs_at tsk (max_arrivals_at tsk t) t := by
  intro hgen tsk htsk t
  unfold task_arrivals_at arrivals_at concrete_arrival_sequence
  rw [bigcat_filter_eq_filter_bigcat]
  exact bigcat_seq_uniqK (fun x => generate_jobs_at x (max_arrivals_at x t) t)
    (fun j => job_task (Task := Task) j)
    (fun x y hy => (hgen x _ t y (decide_eq_true hy)).1) tsk ts (of_decide_eq_true htsk) h_uniq

theorem task_arrivals_at_eq {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (ts : List Task) (h_uniq : ts.Nodup) [MaxArrivals Task]
    (generate_jobs_at : Task → Nat → instant → List Job) :
    (∀ (tsk : Task) (n : Nat) (t : instant), decide (tsk ∈ ts) = true →
      (generate_jobs_at tsk n t).length = n) →
    (∀ (tsk : Task) (n : Nat) (t : instant) (j : Job),
      decide (j ∈ generate_jobs_at tsk n t) = true →
        job_task j = tsk ∧ job_arrival j = t ∧ job_cost j ≤ task_cost tsk) →
      ∀ tsk : Task, decide (tsk ∈ ts) = true → ∀ t : instant,
        (task_arrivals_at (concrete_arrival_sequence generate_jobs_at ts) tsk t).length =
          max_arrivals_at tsk t := by
  intro hsize hgen tsk htsk t
  rw [task_arrivals_at_eq_generate_jobs_at ts h_uniq generate_jobs_at hgen tsk htsk t]
  exact hsize tsk _ t htsk

theorem number_of_task_arrivals_eq {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (ts : List Task) (h_uniq : ts.Nodup) [MaxArrivals Task]
    (generate_jobs_at : Task → Nat → instant → List Job) :
    (∀ (tsk : Task) (n : Nat) (t : instant), decide (tsk ∈ ts) = true →
      (generate_jobs_at tsk n t).length = n) →
    (∀ (tsk : Task) (n : Nat) (t : instant) (j : Job),
      decide (j ∈ generate_jobs_at tsk n t) = true →
        job_task j = tsk ∧ job_arrival j = t ∧ job_cost j ≤ task_cost tsk) →
      ∀ tsk : Task, decide (tsk ∈ ts) = true → ∀ t1 t2 : instant,
        number_of_task_arrivals (concrete_arrival_sequence generate_jobs_at ts) tsk t1 t2 =
          sumSeq (List.range' t1 (t2 - t1)) (fun t => max_arrivals_at tsk t) := by
  intro hsize hgen tsk htsk t1 t2
  unfold number_of_task_arrivals
  refine (size_of_task_arrivals_between (Task := Task)
    (concrete_arrival_sequence generate_jobs_at ts) tsk t1 t2).trans ?_
  exact sumSeq_congr_mem _ _ _ (fun t _ =>
    task_arrivals_at_eq ts h_uniq generate_jobs_at hsize hgen tsk htsk t)

theorem extend_horizon_size {Task : TaskType} [DecidableEq Task] (ts : List Task)
    (_h_uniq : ts.Nodup) [MaxArrivals Task] (tsk : Task) (_htsk : decide (tsk ∈ ts) = true) :
    ∀ t : Nat, (Nat.repeat (extend_arrival_prefix tsk) t []).length = t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [Nat.repeat, extend_arrival_prefix, List.length_append, List.length_singleton, ih]

theorem prefix_up_to_size {Task : TaskType} [DecidableEq Task] (ts : List Task)
    (h_uniq : ts.Nodup) [MaxArrivals Task] (tsk : Task) (htsk : decide (tsk ∈ ts) = true) :
    ∀ t : Nat, (maximal_arrival_prefix tsk t).length = t + 1 := by
  intro t
  exact extend_horizon_size ts h_uniq tsk htsk (t + 1)

private theorem maximal_arrival_prefix_succ {Task : TaskType} [DecidableEq Task]
    [MaxArrivals Task] (tsk : Task) (h : Nat) :
    maximal_arrival_prefix tsk (h + 1) =
      maximal_arrival_prefix tsk h ++ [next_max_arrival tsk (maximal_arrival_prefix tsk h)] := by
  rfl

theorem n_arrivals_at_prefix_inclusion1 {Task : TaskType} [DecidableEq Task]
    (ts : List Task) (h_uniq : ts.Nodup) [MaxArrivals Task] (tsk : Task)
    (htsk : decide (tsk ∈ ts) = true) :
    ∀ t h : Nat, t ≤ h →
      (maximal_arrival_prefix tsk h).getD t 0 = (maximal_arrival_prefix tsk (h + 1)).getD t 0 := by
  intro t h hle
  rw [maximal_arrival_prefix_succ, List.getD_append _ _ _ _
    (by rw [prefix_up_to_size ts h_uniq tsk htsk]; omega')]

theorem n_arrivals_at_prefix_inclusion {Task : TaskType} [DecidableEq Task]
    (ts : List Task) (h_uniq : ts.Nodup) [MaxArrivals Task] (tsk : Task)
    (htsk : decide (tsk ∈ ts) = true) :
    ∀ t h1 h2 : Nat, (decide (t ≤ h1) && decide (h1 ≤ h2)) = true →
      (maximal_arrival_prefix tsk h1).getD t 0 = (maximal_arrival_prefix tsk h2).getD t 0 := by
  intro t h1 h2 hle
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hle
  obtain ⟨h1le, h12⟩ := hle
  induction h2, h12 using Nat.le_induction with
  | base => rfl
  | succ h2 hh ih =>
      rw [ih, n_arrivals_at_prefix_inclusion1 ts h_uniq tsk htsk t h2 (by omega')]

theorem max_arrivals_at_next_max_arrivals_eq {Task : TaskType} [DecidableEq Task]
    (ts : List Task) (h_uniq : ts.Nodup) [MaxArrivals Task] (tsk : Task)
    (htsk : decide (tsk ∈ ts) = true) :
    ∀ t : Nat, 0 < t →
      max_arrivals_at tsk t = next_max_arrival tsk (maximal_arrival_prefix tsk (t - 1)) := by
  intro t ht
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega'⟩
  unfold max_arrivals_at
  rw [maximal_arrival_prefix_succ, Nat.add_sub_cancel]
  rw [List.getD_append_right _ _ _ _ (by rw [prefix_up_to_size ts h_uniq tsk htsk])]
  rw [prefix_up_to_size ts h_uniq tsk htsk, Nat.sub_self]
  rfl

theorem n_arrivals_at_leq {Task : TaskType} [DecidableEq Task] (ts : List Task)
    (h_uniq : ts.Nodup) [MaxArrivals Task]
    (_hvalid : valid_taskset_arrival_curve ts max_arrivals) (tsk : Task)
    (htsk : decide (tsk ∈ ts) = true) :
    ∀ t Δ : Nat, Δ ≤ t →
      max_arrivals_at tsk t ≤
        max_arrivals tsk (Δ + 1) -
          sumSeq (List.range' (t - Δ) (t - (t - Δ))) (fun i => max_arrivals_at tsk i) := by
  intro t Δ hle
  cases t with
  | zero =>
      have hΔ : Δ = 0 := by omega'
      subst hΔ
      simp [max_arrivals_at, maximal_arrival_prefix, Nat.repeat, extend_arrival_prefix,
        next_max_arrival, jobs_remaining, supremum, choose_superior, suffix_sum, sumSeq]
  | succ s =>
      rw [max_arrivals_at_next_max_arrivals_eq ts h_uniq tsk htsk (s + 1) (Nat.succ_pos s),
        Nat.add_sub_cancel]
      set xs := maximal_arrival_prefix tsk s with hxs
      have hlen : xs.length = s + 1 := prefix_up_to_size ts h_uniq tsk htsk s
      set L := (List.range' 0 (xs.length + 1)).map
        (fun Δ => max_arrivals tsk (Δ + 1) - suffix_sum xs Δ) with hL
      have hmem : max_arrivals tsk (Δ + 1) - suffix_sum xs Δ ∈ L := by
        rw [hL]
        exact List.mem_map.2 ⟨Δ, List.mem_range'_1.2 ⟨Nat.zero_le _, by omega'⟩, rfl⟩
      have hsuffix : suffix_sum xs Δ =
          sumSeq (List.range' (s + 1 - Δ) (s + 1 - (s + 1 - Δ)))
            (fun i => max_arrivals_at tsk i) := by
        unfold suffix_sum
        rw [hlen]
        apply sumSeq_congr_mem
        intro i hi
        have hi' := List.mem_range'_1.1 hi
        unfold max_arrivals_at
        rw [hxs]
        exact (n_arrivals_at_prefix_inclusion ts h_uniq tsk htsk i i s
          (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega')).symm
      rw [← hsuffix]
      unfold next_max_arrival jobs_remaining
      rw [← hL]
      cases hsup : supremum (fun a b => decide (a ≤ b)) L with
      | none =>
          exact absurd (supremum_none _ L hsup ▸ hmem) (List.not_mem_nil)
      | some x =>
          have := supremum_spec (fun a b => decide (a ≤ b))
            (fun x => decide_eq_true (Nat.le_refl x))
            (fun x y => by
              rcases Nat.le_total x y with h | h <;> simp [h])
            (fun x y z hxy hyz => decide_eq_true
              (Nat.le_trans (of_decide_eq_true hxy) (of_decide_eq_true hyz)))
            x L hsup _ hmem
          exact of_decide_eq_true this

theorem concrete_is_arrival_curve {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (ts : List Task) (h_uniq : ts.Nodup) [MaxArrivals Task]
    (hvalid : valid_taskset_arrival_curve ts max_arrivals)
    (generate_jobs_at : Task → Nat → instant → List Job) :
    (∀ (tsk : Task) (n : Nat) (t : instant), decide (tsk ∈ ts) = true →
      (generate_jobs_at tsk n t).length = n) →
    (∀ (tsk : Task) (n : Nat) (t : instant) (j : Job),
      decide (j ∈ generate_jobs_at tsk n t) = true →
        job_task j = tsk ∧ job_arrival j = t ∧ job_cost j ≤ task_cost tsk) →
      taskset_respects_max_arrivals (concrete_arrival_sequence generate_jobs_at ts) ts := by
  intro hsize hgen tsk htsk t1 t2 hle
  obtain ⟨_, hmono⟩ := hvalid tsk htsk
  -- windows ending at `t` of length `d` respect the curve
  have key : ∀ d t : Nat, d ≤ t →
      sumSeq (List.range' (t - d) d) (fun i => max_arrivals_at tsk i) ≤ max_arrivals tsk d := by
    intro d
    induction d with
    | zero => intro t _; simp [sumSeq]
    | succ d ih =>
        intro t hdt
        obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega'⟩
        have hsplit : List.range' (u + 1 - (d + 1)) (d + 1) =
            List.range' (u - d) d ++ [u] := by
          rw [show u + 1 - (d + 1) = u - d by omega', ← List.range'_append_1]
          simp only [List.range'_one]
          congr 2
          omega'
        rw [hsplit, sumSeq_append]
        have hS := ih u (by omega')
        have hat := n_arrivals_at_leq ts h_uniq hvalid tsk htsk u d (by omega')
        rw [show u - (u - d) = d by omega'] at hat
        have hm : max_arrivals tsk d ≤ max_arrivals tsk (d + 1) :=
          of_decide_eq_true (hmono d (d + 1) (decide_eq_true (Nat.le_succ d)))
        have hu : sumSeq [u] (fun i => max_arrivals_at tsk i) = max_arrivals_at tsk u := by
          simp [sumSeq]
        rw [hu]
        omega'
  rw [number_of_task_arrivals_eq ts h_uniq generate_jobs_at hsize hgen tsk htsk t1 t2]
  have := key (t2 - t1) t2 (Nat.sub_le _ _)
  rwa [show t2 - (t2 - t1) = t1 by omega'] at this

end Prosa.Implementation.Facts.MaximalArrivalSequence
