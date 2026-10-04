-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/arrival/jitter/task_arrival.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 45)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence

/-!
Task arrivals in jitter-aware schedules (Rocq module `TaskArrivalWithJitter`, which `Export`s `TaskArrival`).

Representation notes (as in the accepted basic `classic/model/arrival/basic/task_arrival.v`):
* The section-local `Let`s (`arrivals_between`, `actual_job_arrival`, `arriving_jobs`, `num_arrivals`,
  `by_arrival_time`, `sorted_jobs`, `nth_job`, `j_first`, `j_last`, `a_first`, `a_last`) are unfolded in the
  statements. As in the source, the jobs are sorted by `job_arrival` (not by their actual arrival).
* MathComp's `sort by_arrival_time s` is `s.mergeSort (fun j j' => decide (job_arrival j ≤ job_arrival j'))`;
  `[seq j <- s | P j]` is `s.filter P`; `size` is `length`; `nth elem s i` is `s.getD i elem`; `x.-1` is
  `x - 1`; a Boolean chain `a <= b < c` in proposition position is `(decide (a ≤ b) && decide (b < c)) = true`.
* Binder lists follow the Rocq contract (e.g. `sorted_arrivals_properties_of_nth` takes no hypothesis and
  `sorted_arrivals_distance_from_first_job` does not take `H_at_least_one_job`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Arrival.Jitter.TaskArrival.TaskArrivalWithJitter

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def is_job_of_tsk {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (tsk : Task) (j : Job) : Bool :=
  is_job_of_task job_task tsk j

def actual_arrivals_of_task_between {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : time) : List Job :=
  (actual_arrivals_between job_arrival job_jitter arr_seq t1 t2).filter (fun j => is_job_of_tsk job_task tsk j)

def num_actual_arrivals_of_task {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : time) : Nat :=
  (actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).length

/-- LEAN_HELPER: defaulted lookup inside the list. -/
private theorem getD_lt {α : Type u} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

/-- LEAN_HELPER: the sorted list is ordered by `job_arrival`. -/
private theorem sorted_pairwise {α : Type v} (key : α → Nat) (s : List α) :
    List.Pairwise (fun a b => decide (key a ≤ key b) = true) (s.mergeSort (fun j j' => decide (key j ≤ key j'))) := by
  apply List.pairwise_mergeSort
  · intro a b c h1 h2; simp only [decide_eq_true_eq] at *; exact Nat.le_trans h1 h2
  · intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; exact Nat.le_total _ _

theorem sorted_arrivals_properties_of_nth {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job) (tsk : Task) (t1 t2 : time) (elem : Job) :
    ∀ idx : Nat,
      idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 →
      (decide (t1 ≤ actual_arrival job_arrival job_jitter (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem)) &&
        decide (actual_arrival job_arrival job_jitter (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) < t2)) = true ∧
      job_task (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) = tsk ∧
      arrives_in arr_seq (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) := by
  intro idx LTidx
  have hidx : idx < ((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).length := by
    rw [List.length_mergeSort]; exact LTidx
  have IN : (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) ∈ actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2 := by
    rw [← List.mem_mergeSort (le := fun j j' => decide (job_arrival j ≤ job_arrival j')), getD_lt hidx]
    exact List.getElem_mem hidx
  generalize ((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
    (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem = x at IN ⊢
  unfold actual_arrivals_of_task_between at IN
  rw [List.mem_filter] at IN
  obtain ⟨INarr, JOB⟩ := IN
  refine ⟨?_, ?_, ?_⟩
  · exact in_actual_arrivals_implies_arrived_between job_arrival job_jitter arr_seq _ t1 t2 INarr
  · simp only [is_job_of_tsk, is_job_of_task, decide_eq_true_eq] at JOB; exact JOB
  · exact in_actual_arrivals_between_implies_arrived job_arrival job_jitter arr_seq _ t1 t2 INarr

theorem sorted_arrivals_current_differs_from_next {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq) (tsk : Task) (t1 t2 : time) (elem : Job) :
    ∀ idx : Nat,
      idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1 →
      (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) ≠ (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD (idx + 1) elem) := by
  intro idx LT
  have hlen : ((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).length = num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 := List.length_mergeSort _
  have hnd : ((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).Nodup := by
    apply (List.mergeSort_perm _ _).nodup_iff.mpr
    exact (actual_arrivals_uniq job_arrival job_jitter arr_seq H_consistent_arrivals H_no_duplicate_arrivals
      t1 t2).filter _
  have h1 : idx < ((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).length := by omega
  have h2 : idx + 1 < ((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).length := by omega
  rw [getD_lt h1, getD_lt h2]
  intro EQ
  have := (List.Nodup.getElem_inj_iff hnd).mp EQ
  omega

theorem sorted_arrivals_separated_by_period {Task : Type u} [DecidableEq Task] (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_jobs : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : Task) (t1 t2 : time) (elem : Job) :
    ∀ idx : Nat,
      idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1 →
      job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) + task_period tsk ≤ job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD (idx + 1) elem) := by
  intro idx LT
  have hlen : ((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).length = num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 := List.length_mergeSort _
  have NTH1 := sorted_arrivals_properties_of_nth job_arrival job_jitter job_task arr_seq tsk t1 t2 elem idx
    (by omega)
  have NTH2 := sorted_arrivals_properties_of_nth job_arrival job_jitter job_task arr_seq tsk t1 t2 elem (idx + 1)
    (by omega)
  have NEQ := sorted_arrivals_current_differs_from_next job_arrival job_jitter job_task arr_seq
    H_consistent_arrivals H_no_duplicate_arrivals tsk t1 t2 elem idx LT
  have h1 : idx < ((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).length := by omega
  have h2 : idx + 1 < ((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).length := by omega
  have ORD : job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) ≤ job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD (idx + 1) elem) := by
    rw [getD_lt h1, getD_lt h2]
    have := List.pairwise_iff_getElem.mp (sorted_pairwise job_arrival
      (actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2)) idx (idx + 1) h1 h2
      (by omega)
    simpa using this
  obtain ⟨_, JOB1, ARR1⟩ := NTH1
  obtain ⟨_, JOB2, ARR2⟩ := NTH2
  have := H_sporadic_jobs _ _ NEQ ARR1 ARR2 (JOB1.trans JOB2.symm) ORD
  rw [JOB1] at this
  exact this

theorem sorted_arrivals_distance_from_first_job {Task : Type u} [DecidableEq Task] (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_jobs : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : Task) (t1 t2 : time) (elem : Job) :
    ∀ idx : Nat,
      idx < num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 →
      job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD 0 elem) + idx * task_period tsk ≤ job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD idx elem) := by
  intro idx
  induction idx with
  | zero => intro _; simp
  | succ idx IH =>
    intro LT
    have SEP := sorted_arrivals_separated_by_period task_period job_arrival job_jitter job_task arr_seq
      H_consistent_arrivals H_no_duplicate_arrivals H_sporadic_jobs tsk t1 t2 elem idx (by omega)
    have := IH (by omega)
    rw [Nat.succ_mul]
    omega'

theorem sorted_arrivals_distance_between_first_and_last {Task : Type u} [DecidableEq Task] (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_jitter : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_consistent_arrivals : arrival_times_are_consistent job_arrival arr_seq)
    (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_jobs : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : Task) (t1 t2 : time) (elem : Job)
    (H_at_least_one_job : 1 ≤ num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2) :
    job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD 0 elem) + (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) * task_period tsk ≤ job_arrival (((actual_arrivals_of_task_between job_arrival job_jitter job_task arr_seq tsk t1 t2).mergeSort
          (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD (num_actual_arrivals_of_task job_arrival job_jitter job_task arr_seq tsk t1 t2 - 1) elem) :=
  sorted_arrivals_distance_from_first_job task_period job_arrival job_jitter job_task arr_seq
    H_consistent_arrivals H_no_duplicate_arrivals H_sporadic_jobs tsk t1 t2 elem _ (by omega)

end Prosa.Classic.Model.Arrival.Jitter.TaskArrival.TaskArrivalWithJitter
