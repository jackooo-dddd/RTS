-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/parallel/workload_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 90)

import Prosa.Util.Sum
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Analysis.Global.Basic.WorkloadBound

/-!
Workload bound for parallel jobs (Rocq module `WorkloadBound` of `classic/analysis/global/parallel/workload_bound.v`).

Representation notes (as in the accepted `classic/analysis/global/basic/workload_bound.v`):
* The section-local `Let`s are unfolded in the statements: `sorted_jobs` is
  `(jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
  (fun x y => decide (job_arrival x ≤ job_arrival y))`, `t2` is `t1 + delta`, `n_k` is
  `max_jobs task_period tsk R_tsk delta`, `workload_bound` is `W task_cost task_period tsk R_tsk delta`,
  `workload_of` is `workload job_task sched`, `job_has_completed_by` is `completed job_cost sched`, and
  `j_fst` / `j_lst` are `sorted_jobs.getD 0 elem` / `sorted_jobs.getD (num_mid_jobs + 1) elem`.
* `div_ceil` is the classic `Prosa.Classic.Util.DivMod.div_ceil`; `\sum_(i <- s) F i` is `sumSeq s F`;
  `\sum_(a <= i < b)` is `∑ i ∈ Finset.Ico a b`; `x != 0` is `(!decide (x = 0)) = true`;
  `(j \in s1) = (j \in s2)` is `decide (j ∈ s1) = decide (j ∈ s2)`.
* Binder lists follow the Rocq contract.
* Proofs: the lemmas whose statements coincide with the accepted basic `WorkloadBound` module are proved by that
  module's lemmas; the others are proved here (`LEAN_HELPER`s are local copies of the basic module's private
  helpers).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Parallel.WorkloadBound.WorkloadBound

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Util.DivMod (div_ceil leq_divceil2r ceil_neq0)
open Prosa.Util.Sum (sumSeq)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def max_jobs {sporadic_task : Type u} [DecidableEq sporadic_task] (task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  div_ceil (delta + R_tsk) (task_period tsk)

def W {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period : sporadic_task → time) (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  max_jobs task_period tsk R_tsk delta * task_cost tsk

theorem W_monotonic {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period : sporadic_task → time) (tsk : sporadic_task)
    (H_period_positive : 0 < task_period tsk) (R1 R2 : time) (H_R1_le_R2 : R1 ≤ R2) :
    ∀ t1 t2 : Nat, t1 ≤ t2 → W task_cost task_period tsk R1 t1 ≤ W task_cost task_period tsk R2 t2 := by
  intro t1 t2 LE
  unfold W max_jobs
  exact Nat.mul_le_mul_right _ (leq_divceil2r _ _ _ H_period_positive (Nat.add_le_add LE H_R1_le_R2))

/-! ### LEAN_HELPER lemmas (local copies of the basic module's private helpers) -/

private theorem getD_lt {α : Type _} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD_eq_getElem?_getD, h]

private theorem sorted_nodup {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 delta : time) :
    ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).Nodup := by
  apply (List.mergeSort_perm _ _).nodup_iff.mpr
  exact (List.nodup_dedup _).filter _

private theorem sumSeq_getD {T : Type _} (l : List T) (F : T → Nat) (x0 : T) :
    sumSeq l F = ∑ i ∈ Finset.Ico 0 l.length, F (l.getD i x0) := by
  rw [← Finset.range_eq_Ico]
  induction l with
  | nil => simp [sumSeq]
  | cons a l ih =>
      unfold sumSeq at ih ⊢
      rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
      simp [Nat.add_comm]

private theorem first_le_last {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → sporadic_task)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 delta : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) ≤ job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) := by
  have := Prosa.Classic.Util.Sorting.prev_le_next job_arrival ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) elem 0 (num_mid_jobs + 1)
    (fun i hi => Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_jobs_ordered_by_arrival job_arrival job_task sched tsk t1 delta i elem hi)
    (by omega)
  simpa using this

private theorem le_div_ceil_mul (x p : Nat) (hp : 0 < p) : x ≤ div_ceil x p * p := by
  unfold div_ceil
  split
  · next h => rw [Nat.div_mul_cancel h]
  · rw [Nat.add_mul, Nat.one_mul]; exact Nat.le_of_lt (Nat.lt_div_mul_add hp)

/-! ### Lemmas -/

theorem workload_bound_simpl_by_sorting_scheduled_jobs {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task)
    (t1 delta : time) :
    workload_joblist job_task sched tsk t1 (t1 + delta) =
      sumSeq ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun i => service_during sched i t1 (t1 + delta)) :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_simpl_by_sorting_scheduled_jobs job_arrival job_task sched tsk t1 delta

theorem workload_bound_job_in_same_sequence {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task)
    (t1 delta : time) (j : Job) :
    decide (j ∈ jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)) = decide (j ∈ ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y)))) :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_job_in_same_sequence job_arrival job_task sched tsk t1 delta j

theorem workload_bound_all_jobs_from_tsk {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (tsk : sporadic_task) (t1 delta : time) :
    ∀ j_i : Job, j_i ∈ ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) →
      arrives_in arr_seq j_i ∧ job_task j_i = tsk ∧
      (!decide (service_during sched j_i t1 (t1 + delta) = 0)) = true ∧
      j_i ∈ jobs_scheduled_between sched t1 (t1 + delta) :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_all_jobs_from_tsk job_arrival job_task arr_seq sched H_jobs_come_from_arrival_sequence tsk t1 delta

theorem workload_bound_jobs_ordered_by_arrival {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task)
    (t1 delta : time) :
    ∀ (i : Nat) (elem : Job), i < ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length - 1 →
      job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD i elem) ≤ job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (i + 1) elem) :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_jobs_ordered_by_arrival job_arrival job_task sched tsk t1 delta

theorem workload_bound_holds_for_at_most_n_k_jobs {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (t1 delta R_tsk : time) :
    ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length ≤ max_jobs task_period tsk R_tsk delta →
    sumSeq ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun i => service_during sched i t1 (t1 + delta)) ≤ W task_cost task_period tsk R_tsk delta := by
  intro LEnk
  have hle : sumSeq ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun i => service_during sched i t1 (t1 + delta)) ≤ ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length * task_cost tsk := by
    unfold sumSeq
    have := List.sum_le_card_nsmul (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).map (fun i => service_during sched i t1 (t1 + delta))) (task_cost tsk) (by
      intro x hx
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx
      obtain ⟨ARR, TSK, _, _⟩ := Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_all_jobs_from_tsk job_arrival job_task arr_seq sched
        H_jobs_come_from_arrival_sequence tsk t1 delta j hj
      exact cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task sched
        H_completed_jobs_dont_execute tsk j TSK (H_jobs_have_valid_parameters j ARR) _ _)
    simpa using this
  unfold W
  exact Nat.le_trans hle (Nat.mul_le_mul_right _ LEnk)

theorem workload_bound_j_fst_is_job_of_tsk {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (tsk : sporadic_task) (t1 delta : time)
    (H_at_least_one_job : 0 < ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length) (elem : Job) :
    arrives_in arr_seq (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) ∧ job_task (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) = tsk ∧
    (!decide (service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) t1 (t1 + delta) = 0)) = true ∧
    ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem ∈ jobs_scheduled_between sched t1 (t1 + delta) :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_j_fst_is_job_of_tsk job_arrival job_task arr_seq sched H_jobs_come_from_arrival_sequence tsk t1
    delta H_at_least_one_job elem

theorem workload_bound_holds_for_a_single_job {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk) (t1 delta R_tsk : time) (H_at_least_one_job : 0 < ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length) (elem : Job) :
    ∑ i ∈ Finset.Ico 0 1, service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD i elem) t1 (t1 + delta) ≤
      W task_cost task_period tsk R_tsk delta := by
  obtain ⟨ARR, TSK, NZ, _⟩ := Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_j_fst_is_job_of_tsk job_arrival job_task arr_seq sched
    H_jobs_come_from_arrival_sequence tsk t1 delta H_at_least_one_job elem
  obtain ⟨_, PERIOD, _, _, _⟩ := H_valid_task_parameters
  have hp : 0 < task_period tsk := by simpa [task_period_positive] using PERIOD
  rw [← Finset.range_eq_Ico, Finset.sum_range_one]
  have hc := cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task sched
    H_completed_jobs_dont_execute tsk _ TSK (H_jobs_have_valid_parameters _ ARR) t1 (t1 + delta)
  have hdelta : 0 < delta := by
    rcases Nat.eq_zero_or_pos delta with h | h
    · exfalso
      subst h
      simp [service_during] at NZ
    · exact h
  have hn := ceil_neq0 (delta + R_tsk) (task_period tsk) (by omega') hp
  unfold W max_jobs
  calc _ ≤ task_cost tsk := hc
    _ = 1 * task_cost tsk := (Nat.one_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ hn

theorem workload_bound_j_lst_is_job_of_tsk {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (tsk : sporadic_task) (t1 delta : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    arrives_in arr_seq (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) ∧ job_task (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) = tsk ∧
    (!decide (service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) t1 (t1 + delta) = 0)) = true ∧
    ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem ∈ jobs_scheduled_between sched t1 (t1 + delta) :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_j_lst_is_job_of_tsk job_arrival job_task arr_seq sched H_jobs_come_from_arrival_sequence tsk t1
    delta num_mid_jobs H_at_least_two_jobs elem

theorem workload_bound_response_time_of_first_job_inside_interval {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival job_cost : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : sporadic_task) (t1 delta R_tsk : time) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + R_tsk < t1 + delta → completed job_cost sched j (job_arrival j + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    t1 ≤ job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) + R_tsk :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_response_time_of_first_job_inside_interval job_arrival job_cost job_task arr_seq sched
    H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1 delta R_tsk H_response_time_bound
    num_mid_jobs H_at_least_two_jobs elem

theorem workload_bound_last_job_arrives_before_end_of_interval {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (tsk : sporadic_task) (t1 delta : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) < t1 + delta :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_last_job_arrives_before_end_of_interval job_arrival job_task arr_seq sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute tsk t1 delta num_mid_jobs H_at_least_two_jobs elem

theorem workload_bound_service_of_middle_jobs {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (t1 delta : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    ∑ i ∈ Finset.Ico 0 num_mid_jobs, service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (i + 1) elem) t1 (t1 + delta) ≤
      num_mid_jobs * task_cost tsk :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_service_of_middle_jobs task_cost task_deadline job_arrival job_cost job_task job_deadline arr_seq
    H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1 delta
    num_mid_jobs H_at_least_two_jobs elem

theorem workload_bound_many_periods_in_between {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (t1 delta R_tsk : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    (num_mid_jobs + 1) * task_period tsk ≤ job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) - job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) := by
  have hlen : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length - 1 = num_mid_jobs + 1 := by omega
  have TEL := Prosa.Classic.Util.Sum.telescoping_sum Job job_arrival ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) elem
    (fun i hi => Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_jobs_ordered_by_arrival job_arrival job_task sched tsk t1 delta i elem hi)
  rw [hlen] at TEL
  rw [TEL]
  have hnd := sorted_nodup job_arrival job_task sched tsk t1 delta
  calc (num_mid_jobs + 1) * task_period tsk
      = ∑ _i ∈ Finset.Ico 0 (num_mid_jobs + 1), task_period tsk := by simp
    _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have h1 : i < ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length := by omega
        have h2 : i + 1 < ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length := by omega
        obtain ⟨CURarr, CURtsk, _, _⟩ := Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_all_jobs_from_tsk job_arrival job_task
          arr_seq sched H_jobs_come_from_arrival_sequence tsk t1 delta (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD i elem)
          (by rw [getD_lt h1]; exact List.getElem_mem _)
        obtain ⟨NEXTarr, NEXTtsk, _, _⟩ := Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_all_jobs_from_tsk job_arrival job_task
          arr_seq sched H_jobs_come_from_arrival_sequence tsk t1 delta (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (i + 1) elem)
          (by rw [getD_lt h2]; exact List.getElem_mem _)
        have ARRle := Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_jobs_ordered_by_arrival job_arrival job_task sched tsk t1
          delta i elem (by omega)
        have DIFF : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD i elem ≠ ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (i + 1) elem := by
          rw [getD_lt h1, getD_lt h2]
          intro EQ
          have := (List.Nodup.getElem_inj_iff hnd).mp EQ
          omega
        have SPO := H_sporadic_tasks _ _ DIFF CURarr NEXTarr (CURtsk.trans NEXTtsk.symm) ARRle
        rw [CURtsk] at SPO
        omega'

theorem workload_bound_n_k_covers_all_jobs {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk)
    (t1 delta R_tsk : time) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + R_tsk < t1 + delta → completed job_cost sched j (job_arrival j + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    num_mid_jobs + 2 ≤ max_jobs task_period tsk R_tsk delta := by
  obtain ⟨_, PERIOD, _, _, _⟩ := H_valid_task_parameters
  have hp : 0 < task_period tsk := by simpa [task_period_positive] using PERIOD
  by_contra LTnk
  have MANY := workload_bound_many_periods_in_between task_cost task_period job_arrival job_task arr_seq sched
    H_jobs_come_from_arrival_sequence H_sporadic_tasks tsk t1 delta R_tsk num_mid_jobs H_at_least_two_jobs elem
  have CEIL := le_div_ceil_mul (delta + R_tsk) (task_period tsk) hp
  have MUL : max_jobs task_period tsk R_tsk delta * task_period tsk ≤ (num_mid_jobs + 1) * task_period tsk :=
    Nat.mul_le_mul_right _ (by omega)
  unfold max_jobs at MUL
  have FIRST := workload_bound_response_time_of_first_job_inside_interval job_arrival job_cost job_task arr_seq sched
    H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1 delta R_tsk H_response_time_bound
    num_mid_jobs H_at_least_two_jobs elem
  have LST := workload_bound_last_job_arrives_before_end_of_interval job_arrival job_task arr_seq sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute tsk t1 delta num_mid_jobs H_at_least_two_jobs elem
  have ORD := first_le_last job_arrival job_task sched tsk t1 delta num_mid_jobs H_at_least_two_jobs elem
  omega'

theorem workload_bound_holds {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk) (t1 delta R_tsk : time) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + R_tsk < t1 + delta → completed job_cost sched j (job_arrival j + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    ∑ i ∈ Finset.Ico 0 (num_mid_jobs + 2), service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD i elem) t1 (t1 + delta) ≤
      W task_cost task_period tsk R_tsk delta := by
  have ALL := workload_bound_n_k_covers_all_jobs task_cost task_period task_deadline job_arrival job_cost job_task
    arr_seq sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_sporadic_tasks tsk H_valid_task_parameters t1 delta R_tsk H_response_time_bound num_mid_jobs H_at_least_two_jobs
    elem
  unfold W
  calc _ ≤ ∑ _i ∈ Finset.Ico 0 (num_mid_jobs + 2), task_cost tsk := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        have hlt : i < ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length := by omega
        obtain ⟨ARR, TSK, _, _⟩ := Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_all_jobs_from_tsk job_arrival job_task arr_seq sched
          H_jobs_come_from_arrival_sequence tsk t1 delta (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD i elem)
          (by rw [getD_lt hlt]; exact List.getElem_mem _)
        exact cumulative_service_le_task_cost task_cost task_deadline job_cost job_deadline job_task sched
          H_completed_jobs_dont_execute tsk _ TSK (H_jobs_have_valid_parameters _ ARR) _ _
    _ = (num_mid_jobs + 2) * task_cost tsk := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ ALL

theorem workload_bounded_by_W {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk) (t1 delta R_tsk : time) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + R_tsk < t1 + delta → completed job_cost sched j (job_arrival j + R_tsk) = true) :
    workload job_task sched tsk t1 (t1 + delta) ≤ W task_cost task_period tsk R_tsk delta := by
  rw [workload_eq_workload_joblist,
    workload_bound_simpl_by_sorting_scheduled_jobs job_arrival job_task sched tsk t1 delta]
  by_cases NUM : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length ≤ max_jobs task_period tsk R_tsk delta
  · exact workload_bound_holds_for_at_most_n_k_jobs task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_completed_jobs_dont_execute tsk t1 delta R_tsk NUM
  obtain ⟨elem, _⟩ := List.exists_mem_of_length_pos (by omega : 0 < ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length)
  rw [sumSeq_getD _ _ elem]
  obtain hlen | ⟨num_mid_jobs, hlen⟩ : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = 1 ∨ ∃ m, ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = m + 2 := by
    rcases h : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length with _ | _ | m
    · omega
    · exact Or.inl rfl
    · exact Or.inr ⟨m, rfl⟩
  · rw [hlen]
    exact workload_bound_holds_for_a_single_job task_cost task_period task_deadline job_arrival job_cost job_task
      job_deadline arr_seq H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence
      H_completed_jobs_dont_execute tsk H_valid_task_parameters t1 delta R_tsk (by omega) elem
  · rw [hlen]
    exact workload_bound_holds task_cost task_period task_deadline job_arrival job_cost job_task job_deadline arr_seq
      H_jobs_have_valid_parameters sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sporadic_tasks tsk H_valid_task_parameters t1 delta R_tsk H_response_time_bound
      num_mid_jobs hlen elem

end Prosa.Classic.Analysis.Global.Parallel.WorkloadBound.WorkloadBound
