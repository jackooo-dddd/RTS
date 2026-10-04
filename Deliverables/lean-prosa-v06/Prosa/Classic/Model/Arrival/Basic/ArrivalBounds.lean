-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/arrival/basic/arrival_bounds.v
-- sha256: see Prosa-Shunqi/classic-prosa/casestudy-translation/file_order.csv (rank 28)

import Prosa.Classic.Util.DivMod
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority

/-!
Upper bound on the number of arrivals of a sporadic task (Rocq module
`ArrivalBounds`).

Representation notes: as in `TaskArrival` (section-local `Let`s unfolded,
`sort` is `List.mergeSort`, `nth` is `getD`, Boolean chains are
`(decide … && decide …) = true`).  `div_ceil` is the classic
`prosa.classic.util.div_mod.div_ceil` (checked with `Set Printing Fully
Qualified` on the Rocq reference build).  Binder lists follow the Rocq contract:
each lemma takes exactly the section hypotheses its Rocq proof uses.
-/

set_option linter.dupNamespace false

namespace Prosa.Classic.Model.Arrival.Basic.ArrivalBounds.ArrivalBounds

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Util.DivMod (div_ceil ceil_neq0)

universe u v

/-- LEAN_HELPER: `omega` after unfolding the classic time aliases. -/
local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

theorem sporadic_arrival_bound_no_jobs {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job] (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (t1 t2 : time) (tsk : Task)
    (H_no_jobs : num_arrivals_of_task job_task arr_seq tsk t1 t2 = 0) :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 ≤ div_ceil (t2 - t1) (task_period tsk) := by
  rw [H_no_jobs]; exact Nat.zero_le _

theorem sporadic_arrival_bound_more_than_one_point {Task : Type u} {Job : Type v}
    [DecidableEq Task] [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (t1 t2 : time) (tsk : Task) :
    0 < num_arrivals_of_task job_task arr_seq tsk t1 t2 →
    t1 < t2 := by
  intro ONE
  unfold num_arrivals_of_task at ONE
  obtain ⟨j, hj⟩ := List.exists_mem_of_length_pos ONE
  unfold arrivals_of_task_between at hj
  rw [List.mem_filter] at hj
  have ARR := in_arrivals_implies_arrived_between job_arrival arr_seq
    H_arrival_times_are_consistent j t1 t2 hj.1
  simp only [arrived_between, Bool.and_eq_true, decide_eq_true_eq] at ARR
  omega'

theorem sporadic_arrival_bound_one_job {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk)
    (H_no_jobs : num_arrivals_of_task job_task arr_seq tsk t1 t2 = 1) :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 ≤ div_ceil (t2 - t1) (task_period tsk) := by
  rw [H_no_jobs]
  have hlt := sporadic_arrival_bound_more_than_one_point job_arrival job_task arr_seq
    H_arrival_times_are_consistent t1 t2 tsk (by omega)
  exact ceil_neq0 (t2 - t1) (task_period tsk) (by omega') H_period_gt_zero

theorem sporadic_arrival_bound_properties_of_nth {Task : Type u} {Job : Type v}
    [DecidableEq Task] [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (t1 t2 : time) (tsk : Task) (elem : Job) :
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
  exact sorted_arrivals_properties_of_nth job_arrival job_task arr_seq
    H_arrival_times_are_consistent tsk t1 t2 elem idx LTidx

theorem sporadic_arrival_bound_distance_between_first_and_last {Task : Type u}
    [DecidableEq Task] (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (t1 t2 : time) (tsk : Task)
    (H_at_least_two_jobs : 2 ≤ num_arrivals_of_task job_task arr_seq tsk t1 t2) (elem : Job) :
    job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
        (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD 0 elem) +
        (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) * task_period tsk ≤
      job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
        (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD
          (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) elem) :=
  sorted_arrivals_distance_between_first_and_last task_period job_arrival job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks tsk t1 t2 elem
    (by omega)

/-- LEAN_HELPER: `x ≤ div_ceil x p * p` for a positive `p`. -/
private theorem le_div_ceil_mul (x p : Nat) (hp : 0 < p) : x ≤ div_ceil x p * p := by
  unfold div_ceil
  split
  · rename_i h; rw [Nat.div_mul_cancel h]
  · have := Nat.lt_div_mul_add (a := x) hp
    rw [Nat.add_mul, Nat.one_mul]; omega

theorem sporadic_arrival_bound_last_job_too_far {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk)
    (H_at_least_two_jobs : 2 ≤ num_arrivals_of_task job_task arr_seq tsk t1 t2)
    (H_many_arrivals :
      div_ceil (t2 - t1) (task_period tsk) < num_arrivals_of_task job_task arr_seq tsk t1 t2)
    (elem : Job) :
    job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
        (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD 0 elem) + t2 - t1 ≤
      job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
        (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD
          (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) elem) := by
  have DIST := sporadic_arrival_bound_distance_between_first_and_last task_period job_arrival
    job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks
    t1 t2 tsk H_at_least_two_jobs elem
  have MORE := sporadic_arrival_bound_more_than_one_point job_arrival job_task arr_seq
    H_arrival_times_are_consistent t1 t2 tsk (by omega)
  have hceil := le_div_ceil_mul (t2 - t1) (task_period tsk) H_period_gt_zero
  have hmul : div_ceil (t2 - t1) (task_period tsk) * task_period tsk ≤
      (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) * task_period tsk :=
    Nat.mul_le_mul_right _ (by omega)
  omega'

theorem sporadic_arrival_bound_last_arrives_too_late {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk)
    (H_at_least_two_jobs : 2 ≤ num_arrivals_of_task job_task arr_seq tsk t1 t2)
    (H_many_arrivals :
      div_ceil (t2 - t1) (task_period tsk) < num_arrivals_of_task job_task arr_seq tsk t1 t2)
    (elem : Job) :
    t2 ≤ job_arrival (((arrivals_of_task_between job_task arr_seq tsk t1 t2).mergeSort
        (fun j j' => decide (job_arrival j ≤ job_arrival j'))).getD
          (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) elem) := by
  have NTH := sporadic_arrival_bound_properties_of_nth job_arrival job_task arr_seq
    H_arrival_times_are_consistent t1 t2 tsk elem 0 (by omega)
  have TOOFAR := sporadic_arrival_bound_last_job_too_far task_period job_arrival job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk
    H_period_gt_zero H_at_least_two_jobs H_many_arrivals elem
  simp only [Bool.and_eq_true, decide_eq_true_eq] at NTH
  omega'

theorem sporadic_arrival_bound_case_3_contradiction {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk)
    (H_at_least_two_jobs : 2 ≤ num_arrivals_of_task job_task arr_seq tsk t1 t2)
    (H_many_arrivals :
      div_ceil (t2 - t1) (task_period tsk) < num_arrivals_of_task job_task arr_seq tsk t1 t2)
    (elem : Job) : False := by
  have LATE := sporadic_arrival_bound_last_arrives_too_late task_period job_arrival job_task
    arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk
    H_period_gt_zero H_at_least_two_jobs H_many_arrivals elem
  have NTH := sporadic_arrival_bound_properties_of_nth job_arrival job_task arr_seq
    H_arrival_times_are_consistent t1 t2 tsk elem
    (num_arrivals_of_task job_task arr_seq tsk t1 t2 - 1) (by omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at NTH
  omega'

theorem sporadic_task_arrival_bound_at_least_two_jobs {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk)
    (H_at_least_two_jobs : 2 ≤ num_arrivals_of_task job_task arr_seq tsk t1 t2) :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 ≤ div_ceil (t2 - t1) (task_period tsk) := by
  by_contra MANY
  have hlen : 0 < (arrivals_of_task_between job_task arr_seq tsk t1 t2).length := by
    unfold num_arrivals_of_task at H_at_least_two_jobs; omega
  obtain ⟨elem, _⟩ := List.exists_mem_of_length_pos hlen
  exact sporadic_arrival_bound_case_3_contradiction task_period job_arrival job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk
    H_period_gt_zero H_at_least_two_jobs (by omega) elem

theorem sporadic_task_arrival_bound {Task : Type u} [DecidableEq Task]
    (task_period : Task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (t1 t2 : time) (tsk : Task) (H_period_gt_zero : 0 < task_period tsk) :
    num_arrivals_of_task job_task arr_seq tsk t1 t2 ≤ div_ceil (t2 - t1) (task_period tsk) := by
  rcases Nat.lt_or_ge (num_arrivals_of_task job_task arr_seq tsk t1 t2) 2 with h | h
  · rcases Nat.lt_or_ge (num_arrivals_of_task job_task arr_seq tsk t1 t2) 1 with h0 | h1
    · exact sporadic_arrival_bound_no_jobs task_period job_task arr_seq t1 t2 tsk (by omega)
    · exact sporadic_arrival_bound_one_job task_period job_arrival job_task arr_seq
        H_arrival_times_are_consistent t1 t2 tsk H_period_gt_zero (by omega)
  · exact sporadic_task_arrival_bound_at_least_two_jobs task_period job_arrival job_task arr_seq
      H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_tasks t1 t2 tsk
      H_period_gt_zero h

end Prosa.Classic.Model.Arrival.Basic.ArrivalBounds.ArrivalBounds
