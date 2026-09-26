-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/facts/model/task_arrivals.v

import Prosa.Model.Task.Arrivals
import Prosa.Util.All
import Prosa.Analysis.Facts.Behavior.Arrivals

namespace Prosa.Analysis.Facts.Model.TaskArrivals

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Util.Notation
open Prosa.Util.Bigcat
open Prosa.Util.List
open Prosa.Util.Sum
open Prosa.Analysis.Facts.Behavior.Arrivals

/-- Membership in a task-filtered arrival list. -/
private theorem mem_task_arrivals_between {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : Nat) (j : Job) :
    j ∈ task_arrivals_between arr_seq tsk t1 t2 ↔
      j ∈ arrivals_between arr_seq t1 t2 ∧ job_task j = tsk := by
  simp [task_arrivals_between, List.mem_filter, job_of_task]

theorem num_arrivals_of_task_cat {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t t1 t2 : Nat),
      (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      number_of_task_arrivals arr_seq tsk t1 t2 =
        number_of_task_arrivals arr_seq tsk t1 t + number_of_task_arrivals arr_seq tsk t t2 := by
  intro tsk t t1 t2 h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [number_of_task_arrivals, task_arrivals_between,
    arrivals_between_cat arr_seq t1 t t2 h.1 h.2, List.filter_append, List.length_append]

theorem task_arrivals_between_cat {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t1 t t2 : Nat), t1 ≤ t → t ≤ t2 →
      task_arrivals_between arr_seq tsk t1 t2 =
        task_arrivals_between arr_seq tsk t1 t ++ task_arrivals_between arr_seq tsk t t2 := by
  intro tsk t1 t t2 h1 h2
  simp only [task_arrivals_between, arrivals_between_cat arr_seq t1 t t2 h1 h2, List.filter_append]

theorem task_arrivals_up_to_prefix_cat {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    ∀ j1 j2 : Job,
      arrives_in arr_seq j1 → arrives_in arr_seq j2 →
      job_task (Task := Task) j1 = job_task (Task := Task) j2 →
      job_arrival j1 ≤ job_arrival j2 →
      prefix_of (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j1)
        (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j2) := by
  intro j1 j2 _ _ htsk hle
  refine ⟨task_arrivals_between arr_seq (job_task (Task := Task) j1)
    (job_arrival j1 + 1) (job_arrival j2 + 1), ?_⟩
  simp only [task_arrivals_up_to_job_arrival, task_arrivals_up_to, ← htsk]
  exact (task_arrivals_between_cat arr_seq _ 0 (job_arrival j1 + 1) (job_arrival j2 + 1)
    (Nat.zero_le _) (Nat.succ_le_succ hle)).symm

theorem arrives_in_task_arrivals_up_to {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ j : Job, arrives_in arr_seq j →
        decide (j ∈ task_arrivals_up_to_job_arrival (Task := Task) arr_seq j) = true := by
  intro hc j harr
  have hin := job_in_arrivals_between arr_seq hc j 0 (job_arrival j + 1) harr (Nat.zero_le _)
    (Nat.lt_succ_self _)
  simp only [decide_eq_true_eq] at hin ⊢
  exact (mem_task_arrivals_between arr_seq _ _ _ j).2 ⟨hin, rfl⟩

theorem arrives_in_task_arrivals_at {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ j : Job, arrives_in arr_seq j →
        decide (j ∈ task_arrivals_at_job_arrival (Task := Task) arr_seq j) = true := by
  intro hc j ⟨t, ht⟩
  have heq := hc j t ht
  simp only [decide_eq_true_eq, task_arrivals_at_job_arrival, task_arrivals_at, List.mem_filter,
    job_of_task, decide_eq_true_eq, and_true]
  simp only [arrives_at, decide_eq_true_eq] at ht
  rw [heq]; exact ht

theorem task_arrivals_cat {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t_m t : Nat), t_m ≤ t →
      task_arrivals_up_to arr_seq tsk t =
        task_arrivals_up_to arr_seq tsk t_m ++ task_arrivals_between arr_seq tsk (t_m + 1) (t + 1) := by
  intro tsk t_m t h
  exact task_arrivals_between_cat arr_seq tsk 0 (t_m + 1) (t + 1) (Nat.zero_le _) (Nat.succ_le_succ h)

theorem task_arrivals_up_to_cat {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    ∀ j : Job, arrives_in arr_seq j →
      task_arrivals_up_to_job_arrival (Task := Task) arr_seq j =
        task_arrivals_before_job_arrival (Task := Task) arr_seq j ++
          task_arrivals_at_job_arrival (Task := Task) arr_seq j := by
  intro j _
  simp only [task_arrivals_up_to_job_arrival, task_arrivals_before_job_arrival,
    task_arrivals_at_job_arrival, task_arrivals_up_to, task_arrivals_before]
  rw [task_arrivals_between_cat arr_seq _ 0 (job_arrival j) (job_arrival j + 1)
    (Nat.zero_le _) (Nat.le_succ _)]
  congr 1
  simp [task_arrivals_between, task_arrivals_at, arrivals_between, bigCat]

theorem job_in_task_arrivals_between {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (tsk : Task) (j : Job) (t1 t2 : Nat),
        arrives_in arr_seq j → job_task j = tsk →
        (decide (t1 ≤ job_arrival j) && decide (job_arrival j < t2)) = true →
        decide (j ∈ task_arrivals_between arr_seq tsk t1 t2) = true := by
  intro hc tsk j t1 t2 harr htsk h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have hin := job_in_arrivals_between arr_seq hc j t1 t2 harr h.1 h.2
  simp only [decide_eq_true_eq] at hin ⊢
  exact (mem_task_arrivals_between arr_seq _ _ _ j).2 ⟨hin, htsk⟩

theorem task_arrivals_between_subset {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t1 t2 : instant) (j : Job),
      decide (j ∈ task_arrivals_between arr_seq tsk t1 t2) = true →
        decide (j ∈ arrivals_between arr_seq t1 t2) = true := by
  intro tsk t1 t2 j h
  simp only [decide_eq_true_eq] at h ⊢
  exact ((mem_task_arrivals_between arr_seq _ _ _ j).1 h).1

theorem arrives_in_task_arrivals_implies_arrived {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t1 t2 : instant) (j : Job),
      decide (j ∈ task_arrivals_between arr_seq tsk t1 t2) = true → arrives_in arr_seq j :=
  fun tsk t1 t2 j h =>
    in_arrivals_implies_arrived arr_seq j t1 t2 (task_arrivals_between_subset arr_seq tsk t1 t2 j h)

theorem arrives_in_task_arrivals_before_implies_arrives_before {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (tsk : Task) (j : Job) (t : instant),
        decide (j ∈ task_arrivals_before arr_seq tsk t) = true → job_arrival j < t := by
  intro hc tsk j t h
  have h' := in_arrivals_implies_arrived_between arr_seq hc j 0 t
    (task_arrivals_between_subset arr_seq tsk 0 t j h)
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at h'
  exact h'.2

theorem arrives_in_task_arrivals_implies_job_task {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (j : Job) (t : instant),
      decide (j ∈ task_arrivals_before arr_seq tsk t) = true →
        decide (job_task j = tsk) = true := by
  intro tsk j t h
  simp only [decide_eq_true_eq] at h ⊢
  exact ((mem_task_arrivals_between arr_seq _ _ _ j).1 h).2

theorem in_task_arrivals_between_implies_job_of_task {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t1 t2 : instant) (j : Job),
      decide (j ∈ task_arrivals_between arr_seq tsk t1 t2) = true → job_task j = tsk := by
  intro tsk t1 t2 j h
  simp only [decide_eq_true_eq] at h
  exact ((mem_task_arrivals_between arr_seq _ _ _ j).1 h).2

theorem task_arrivals_nonempty {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t1 t2 : instant) (j : Job),
      decide (j ∈ task_arrivals_between arr_seq tsk t1 t2) = true → t1 < t2 :=
  fun tsk t1 t2 j h =>
    arrivals_between_nonempty arr_seq t1 t2 j (task_arrivals_between_subset arr_seq tsk t1 t2 j h)

theorem number_of_task_arrivals_nonzero {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t1 t2 : instant),
      0 < number_of_task_arrivals arr_seq tsk t1 t2 → t1 < t2 := by
  intro tsk t1 t2 h
  unfold number_of_task_arrivals at h
  cases hl : task_arrivals_between arr_seq tsk t1 t2 with
  | nil => rw [hl] at h; exact absurd h (Nat.lt_irrefl 0)
  | cons j _ =>
      apply task_arrivals_nonempty arr_seq tsk t1 t2 j
      rw [hl]; simp

theorem uniq_task_arrivals {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (tsk : Task) (t : instant),
        arrival_sequence_uniq arr_seq → (task_arrivals_up_to arr_seq tsk t).Nodup := by
  intro hc tsk t hu
  exact List.Nodup.filter _ (arrivals_uniq arr_seq hc hu 0 (t + 1))

theorem task_arrivals_between_uniq {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (tsk : Task) (t1 t2 : instant),
        arrival_sequence_uniq arr_seq → (task_arrivals_between arr_seq tsk t1 t2).Nodup := by
  intro hc tsk t1 t2 hu
  exact List.Nodup.filter _ (arrivals_uniq arr_seq hc hu t1 t2)

theorem job_notin_task_arrivals_before {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (j : Job) (t : Nat), arrives_in arr_seq j → t < job_arrival j →
        (!decide (j ∈ task_arrivals_up_to arr_seq (job_task (Task := Task) j) t)) = true := by
  intro hc j t _ hlt
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  intro hin
  have hb := ((mem_task_arrivals_between arr_seq _ _ _ j).1 hin).1
  have h' := in_arrivals_implies_arrived_between arr_seq hc j 0 (t + 1) (decide_eq_true hb)
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at h'
  dsimp only [instant] at *
  omega

theorem arrival_lt_implies_strict_prefix {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (tsk : Task) (j1 j2 : Job),
        job_task j1 = tsk → job_task j2 = tsk →
        arrives_in arr_seq j1 → arrives_in arr_seq j2 →
        job_arrival j1 < job_arrival j2 →
        strict_prefix_of (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j1)
          (task_arrivals_up_to_job_arrival (Task := Task) arr_seq j2) := by
  intro hc tsk j1 j2 h1 h2 _ harr2 hlt
  refine ⟨task_arrivals_between arr_seq tsk (job_arrival j1 + 1) (job_arrival j2 + 1), ?_, ?_⟩
  · intro hnil
    have hin := job_in_task_arrivals_between arr_seq hc tsk j2 (job_arrival j1 + 1)
      (job_arrival j2 + 1) harr2 h2 (by simp; omega)
    rw [hnil] at hin; simp at hin
  · simp only [task_arrivals_up_to_job_arrival, h1, h2]
    exact (task_arrivals_cat arr_seq tsk (job_arrival j1) (job_arrival j2) (Nat.le_of_lt hlt)).symm

theorem nth_job_of_task_arrivals {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (tsk : Task) (n : Nat) (j_def j : Job) (t : Nat),
        arrives_in arr_seq j → job_task j = tsk →
        job_index (Task := Task) arr_seq j = n → job_arrival j ≤ t →
        (task_arrivals_up_to arr_seq tsk t).getD n j_def = j := by
  intro hc tsk n j_def j t harr htsk hidx hle
  have hcat := task_arrivals_cat arr_seq tsk (job_arrival j) t hle
  have hmem : j ∈ task_arrivals_up_to arr_seq tsk (job_arrival j) := by
    have := arrives_in_task_arrivals_up_to (Task := Task) arr_seq hc j harr
    simp only [decide_eq_true_eq, task_arrivals_up_to_job_arrival, htsk] at this
    exact this
  have hidx' : (task_arrivals_up_to arr_seq tsk t).idxOf j = n := by
    rw [hcat, List.idxOf_append_of_mem hmem, ← hidx]
    simp [job_index, task_arrivals_up_to_job_arrival, htsk]
  have hmemt : j ∈ task_arrivals_up_to arr_seq tsk t := by
    rw [hcat]; exact List.mem_append_left _ hmem
  rw [← hidx', List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hmemt)]
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hmemt)

theorem task_arrivals_between_is_cat_of_task_arrivals_at {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t1 t2 : instant),
      task_arrivals_between arr_seq tsk t1 t2 = bigCat t1 t2 (fun t => task_arrivals_at arr_seq tsk t) := by
  intro tsk t1 t2
  exact bigcat_nat_filter_eq_filter_bigcat_nat _ _ t1 t2

/-- The source's `\sum_(t1 <= t < t2)` is a sum over `index_iota t1 t2`,
represented by `sumSeq (List.range' t1 (t2 - t1))`. -/
theorem size_of_task_arrivals_between {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task]
    (arr_seq : arrival_sequence Job) :
    ∀ (tsk : Task) (t1 t2 : instant),
      (task_arrivals_between arr_seq tsk t1 t2).length =
        sumSeq (List.range' t1 (t2 - t1)) (fun t => (task_arrivals_at arr_seq tsk t).length) := by
  intro tsk t1 t2
  rw [task_arrivals_between_is_cat_of_task_arrivals_at]
  unfold bigCat sumSeq
  simp [List.length_flatten, List.range'_eq_map_range, List.map_map, Function.comp_def]

theorem task_arrivals_between_sorted {Job : JobType} [DecidableEq Job]
    {Task : TaskType} [DecidableEq Task] [JobTask Job Task] [JobArrival Job]
    (arr_seq : arrival_sequence Job) :
    consistent_arrival_times arr_seq →
      ∀ (tsk : Task) (t1 t2 : instant),
        List.IsChain (fun a b => by_arrival_times a b = true)
          (task_arrivals_between arr_seq tsk t1 t2) := by
  intro hc tsk t1 t2
  have hs := arrivals_between_sorted arr_seq hc t1 t2
  have htrans : ∀ a b c : Job, by_arrival_times a b = true → by_arrival_times b c = true →
      by_arrival_times a c = true := by
    intro a b c hab hbc
    simp only [by_arrival_times, decide_eq_true_eq] at hab hbc ⊢
    exact Nat.le_trans hab hbc
  have : IsTrans Job (fun a b => by_arrival_times a b = true) := ⟨htrans⟩
  have hpw := List.isChain_iff_pairwise.1 hs
  exact (hpw.filter _).isChain

end Prosa.Analysis.Facts.Model.TaskArrivals
