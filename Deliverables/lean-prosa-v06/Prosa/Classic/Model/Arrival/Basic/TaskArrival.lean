-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/arrival/basic/task_arrival.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 25)

import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Mathlib.Data.List.Sort

/-!
Properties of job arrivals of tasks (Rocq module `TaskArrival`).

Representation notes:
* Binder lists follow the Rocq contract (`About` on the Rocq 9.3 reference
  build), including which section hypotheses each lemma takes.
* The section-local `Let`s (`arrivals_between`, `arriving_jobs`, `num_arrivals`,
  `by_arrival_time`, `sorted_jobs`, `nth_job`, `j_first`, …) are unfolded in the
  statements, as Rocq does when the sections are closed.
* MathComp's `sort by_arrival_time s` (a stable merge sort) is
  `s.mergeSort (fun j j' => decide (job_arrival j ≤ job_arrival j'))`, which is
  also stable; for this total preorder both produce the same list.
* `job_task j == tsk` is `decide (job_task j = tsk)`; `[seq j <- s | P j]` is
  `s.filter P`; `nth elem s i` is `s.getD i elem`; `x.-1` is `x - 1`; a Boolean
  chain `a <= b < c` in proposition position is
  `(decide (a ≤ b) && decide (b < c)) = true`.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence

universe u v

/-- LEAN_HELPER: `omega` after unfolding the classic time aliases (as the v0.6
files do with their `omega'` macro). -/
local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def sporadic_task_model {Task : Type u} [DecidableEq Task] (task_period : Task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) : Prop :=
  ∀ (j j' : Job),
    j ≠ j' →
    arrives_in arr_seq j →
    arrives_in arr_seq j' →
    job_task j = job_task j' →
    job_arrival j ≤ job_arrival j' →
    job_arrival j + task_period (job_task j) ≤ job_arrival j'

def is_job_of_task {Task : Type u} {Job : Type v} [DecidableEq Task] [DecidableEq Job]
    (job_task : Job → Task) (tsk : Task) (j : Job) : Bool :=
  decide (job_task j = tsk)

def arrivals_of_task_between {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task)
    (t1 t2 : time) : List Job :=
  (jobs_arrived_between arr_seq t1 t2).filter (is_job_of_task job_task tsk)

def arrivals_of_task_before {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task)
    (t : time) : List Job :=
  arrivals_of_task_between job_task arr_seq tsk 0 t

def num_arrivals_of_task {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task)
    (t1 t2 : time) : Nat :=
  (arrivals_of_task_between job_task arr_seq tsk t1 t2).length

theorem num_arrivals_of_task_cat {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task) :
    ∀ t t1 t2 : Nat,
      (decide (t1 ≤ t) && decide (t ≤ t2)) = true →
      num_arrivals_of_task job_task arr_seq tsk t1 t2 =
        num_arrivals_of_task job_task arr_seq tsk t1 t +
          num_arrivals_of_task job_task arr_seq tsk t t2 := by
  intro t t1 t2 H
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H
  simp only [num_arrivals_of_task, arrivals_of_task_between,
    job_arrived_between_cat arr_seq t1 t t2 H.1 H.2, List.filter_append, List.length_append]

/-! ### Distance between sporadically released jobs -/

/-- LEAN_HELPER: the sorted jobs of `tsk` arriving in `[t1, t2)` (unfolded in statements). -/
private abbrev sortedJobs {Task : Type u} {Job : Type v} [DecidableEq Task] [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (tsk : Task) (t1 t2 : time) : List Job :=
  (arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
    (fun j j' => decide (job_arrival j ≤ job_arrival j'))

private theorem sortedJobs_length {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : time) :
    (sortedJobs job_arrival job_task arr_seq tsk t1 t2).length =
      num_arrivals_of_task job_task arr_seq tsk t1 t2 :=
  List.length_mergeSort _

private theorem sortedJobs_mem {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : time) (j : Job) :
    j ∈ sortedJobs job_arrival job_task arr_seq tsk t1 t2 ↔
      j ∈ arrivals_of_task_between job_task arr_seq tsk t1 t2 :=
  List.mem_mergeSort

private theorem sortedJobs_pairwise {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : time) :
    List.Pairwise (fun a b => decide (job_arrival a ≤ job_arrival b) = true)
      (sortedJobs job_arrival job_task arr_seq tsk t1 t2) := by
  apply List.pairwise_mergeSort
  · intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact Nat.le_trans h1 h2
  · intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _

/-- LEAN_HELPER: defaulted lookup inside the list. -/
private theorem getD_lt {α : Type u} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem sorted_arrivals_properties_of_nth {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (tsk : Task) (t1 t2 : time) (elem : Job) :
    ∀ idx : Nat,
      idx < num_arrivals_of_task job_task arr_seq tsk t1 t2 →
      (decide (t1 ≤ job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem)) &&
        decide (job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) < t2)) = true ∧
      job_task (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) = tsk ∧
      arrives_in arr_seq (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) := by
  intro idx LTidx
  have hlen := sortedJobs_length job_arrival job_task arr_seq tsk t1 t2
  have hidx : idx < (sortedJobs job_arrival job_task arr_seq tsk t1 t2).length := by omega
  have IN : (sortedJobs job_arrival job_task arr_seq tsk t1 t2).getD idx elem ∈
      arrivals_of_task_between job_task arr_seq tsk t1 t2 := by
    rw [← sortedJobs_mem job_arrival, getD_lt hidx]
    exact List.getElem_mem hidx
  unfold arrivals_of_task_between at IN
  rw [List.mem_filter] at IN
  obtain ⟨INarr, JOB⟩ := IN
  refine ⟨?_, ?_, ?_⟩
  · exact in_arrivals_implies_arrived_between job_arrival arr_seq H_consistent_arrivals _ t1 t2
      INarr
  · simpa [is_job_of_task] using JOB
  · exact in_arrivals_implies_arrived arr_seq _ t1 t2 INarr

/-- LEAN_HELPER: the sorted jobs have no duplicates. -/
private theorem sortedJobs_nodup {Task : Type u} {Job : Type v} [DecidableEq Task]
    [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (tsk : Task) (t1 t2 : time) :
    (sortedJobs job_arrival job_task arr_seq tsk t1 t2).Nodup := by
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  exact (arrivals_uniq job_arrival arr_seq H_consistent_arrivals H_no_duplicate_arrivals t1 t2).filter _

theorem sorted_arrivals_current_differs_from_next {Task : Type u} {Job : Type v}
    [DecidableEq Task] [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (tsk : Task) (t1 t2 : time) (elem : Job) :
    ∀ idx : Nat,
      idx < num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1 →
      ((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem ≠
        ((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD (idx + 1) elem := by
  intro idx LT
  have hlen := sortedJobs_length job_arrival job_task arr_seq tsk t1 t2
  have hnd := sortedJobs_nodup job_arrival job_task arr_seq H_consistent_arrivals
    H_no_duplicate_arrivals tsk t1 t2
  have h1 : idx < (sortedJobs job_arrival job_task arr_seq tsk t1 t2).length := by omega
  have h2 : idx + 1 < (sortedJobs job_arrival job_task arr_seq tsk t1 t2).length := by omega
  show (sortedJobs job_arrival job_task arr_seq tsk t1 t2).getD idx elem ≠
    (sortedJobs job_arrival job_task arr_seq tsk t1 t2).getD (idx + 1) elem
  rw [getD_lt h1, getD_lt h2]
  intro EQ
  have := (List.Nodup.getElem_inj_iff hnd).mp EQ
  omega

theorem sorted_arrivals_separated_by_period {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_jobs : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : Task) (t1 t2 : time) (elem : Job) :
    ∀ idx : Nat,
      idx < num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1 →
      job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) +
          task_period tsk ≤
        job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD (idx + 1) elem) := by
  intro idx LT
  have hlen := sortedJobs_length job_arrival job_task arr_seq tsk t1 t2
  have NTH1 := sorted_arrivals_properties_of_nth job_arrival job_task arr_seq
    H_consistent_arrivals tsk t1 t2 elem idx (by omega)
  have NTH2 := sorted_arrivals_properties_of_nth job_arrival job_task arr_seq
    H_consistent_arrivals tsk t1 t2 elem (idx + 1) (by omega)
  have NEQ := sorted_arrivals_current_differs_from_next job_arrival job_task arr_seq
    H_consistent_arrivals H_no_duplicate_arrivals tsk t1 t2 elem idx LT
  have h1 : idx < (sortedJobs job_arrival job_task arr_seq tsk t1 t2).length := by omega
  have h2 : idx + 1 < (sortedJobs job_arrival job_task arr_seq tsk t1 t2).length := by omega
  have ORD : job_arrival ((sortedJobs job_arrival job_task arr_seq tsk t1 t2).getD idx elem) ≤
      job_arrival ((sortedJobs job_arrival job_task arr_seq tsk t1 t2).getD (idx + 1) elem) := by
    rw [getD_lt h1, getD_lt h2]
    have := List.pairwise_iff_getElem.mp (sortedJobs_pairwise job_arrival job_task arr_seq tsk t1 t2)
      idx (idx + 1) h1 h2 (by omega)
    simpa using this
  obtain ⟨_, JOB1, ARR1⟩ := NTH1
  obtain ⟨_, JOB2, ARR2⟩ := NTH2
  have := H_sporadic_jobs _ _ NEQ ARR1 ARR2 (JOB1.trans JOB2.symm) ORD
  rw [JOB1] at this
  exact this

theorem sorted_arrivals_distance_from_first_job {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_jobs : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : Task) (t1 t2 : time) (elem : Job) :
    ∀ idx : Nat,
      idx < num_arrivals_of_task job_task arr_seq tsk t1 t2 →
      job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD 0 elem) +
          idx * task_period tsk ≤
        job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) := by
  intro idx
  induction idx with
  | zero => intro _; simp
  | succ idx IH =>
      intro LT
      have IH' := IH (by omega)
      have SEP := sorted_arrivals_separated_by_period task_period job_arrival job_task arr_seq
        H_consistent_arrivals H_no_duplicate_arrivals H_sporadic_jobs tsk t1 t2 elem idx (by omega)
      rw [Nat.succ_mul]
      omega'

theorem sorted_arrivals_distance_between_first_and_last {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_jobs : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : Task) (t1 t2 : time) (elem : Job)
    (H_at_least_one_job : 1 ≤ num_arrivals_of_task job_task arr_seq tsk t1 t2) :
    job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
        (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD 0 elem) +
        (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) * task_period tsk ≤
      job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
        (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD
          (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) elem) :=
  sorted_arrivals_distance_from_first_job task_period job_arrival job_task arr_seq
    H_consistent_arrivals H_no_duplicate_arrivals H_sporadic_jobs tsk t1 t2 elem _ (by omega)

end Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
