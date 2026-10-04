-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/jitter/workload_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 89)

import Prosa.Util.Sum
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Jitter.Job
import Prosa.Classic.Model.Schedule.Global.Jitter.Schedule
import Prosa.Classic.Analysis.Global.Basic.WorkloadBound

/-!
Bertogna and Cirinei's workload bound with release jitter (Rocq module `WorkloadBoundJitter`).

Representation notes (as in the accepted `classic/analysis/global/basic/workload_bound.v`):
* The section-local `Let`s are unfolded in the statements: `sorted_jobs` is
  `(jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
  (fun x y => decide (job_arrival x ≤ job_arrival y))`, `t2` is `t1 + delta`, `n_k` is
  `max_jobs_jitter task_cost task_period task_jitter tsk R_tsk delta`, `workload_bound` is
  `W_jitter task_cost task_period task_jitter tsk R_tsk delta`, `workload_of` is `workload job_task sched`,
  `job_has_completed_by` is `completed job_cost sched`, and `j_fst` / `j_lst` are `sorted_jobs.getD 0 elem` /
  `sorted_jobs.getD (num_mid_jobs + 1) elem`.
* The `let e_k := … in let p_k := … in` of `W_jitter` is inlined; `minn` is `min`; `x.-1` is `x - 1`;
  `\sum_(i <- s) F i` is `sumSeq s F`; `\sum_(a <= i < b)` is `∑ i ∈ Finset.Ico a b`; `x != 0` is
  `(!decide (x = 0)) = true`; `(j \in s1) = (j \in s2)` is `decide (j ∈ s1) = decide (j ∈ s2)`.
* As in the source, the hypothesis named `H_jobs_must_arrive_to_execute` has type
  `jobs_execute_after_jitter job_arrival job_jitter sched`.
* Binder lists follow the Rocq contract.
* Proofs: every lemma is the corresponding lemma of the accepted basic `WorkloadBound` module instantiated with
  response-time bound `task_jitter tsk + R_tsk` (jitter-aware hypotheses are converted by the `LEAN_HELPER`s below).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Jitter.WorkloadBound.WorkloadBoundJitter

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Jitter.Job.JobWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter (jobs_execute_after_jitter arrival_before_jitter)
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Util.DivMod (div_floor)
open Prosa.Util.Sum (sumSeq)

universe u v

def max_jobs_jitter {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_jitter : sporadic_task → time)
    (tsk : sporadic_task) (R_tsk delta : time) : Nat :=
  div_floor (delta + task_jitter tsk + R_tsk - task_cost tsk) (task_period tsk)

def W_jitter {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_jitter : sporadic_task → time) (tsk : sporadic_task)
    (R_tsk delta : time) : Nat :=
  min (task_cost tsk)
      (delta + task_jitter tsk + R_tsk - task_cost tsk -
        max_jobs_jitter task_cost task_period task_jitter tsk R_tsk delta * task_period tsk) +
    max_jobs_jitter task_cost task_period task_jitter tsk R_tsk delta * task_cost tsk

/-! ### LEAN_HELPER conversions to the basic workload bound -/

private theorem max_jobs_jitter_eq {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_jitter : sporadic_task → time)
    (tsk : sporadic_task) (R_tsk delta : time) :
    max_jobs_jitter task_cost task_period task_jitter tsk R_tsk delta =
      Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.max_jobs task_cost task_period tsk (task_jitter tsk + R_tsk) delta := by
  unfold max_jobs_jitter Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.max_jobs
  rw [Nat.add_assoc delta]

private theorem W_jitter_eq {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_jitter : sporadic_task → time)
    (tsk : sporadic_task) (R_tsk delta : time) :
    W_jitter task_cost task_period task_jitter tsk R_tsk delta =
      Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.W task_cost task_period tsk (task_jitter tsk + R_tsk) delta := by
  unfold W_jitter Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.W
  rw [max_jobs_jitter_eq, Nat.add_assoc delta]

private theorem valid_of_jitter {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (arr_seq : arrival_sequence Job)
    (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j) :
    ∀ j : Job, arrives_in arr_seq j → valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j :=
  fun j ARR => (H_jobs_have_valid_parameters j ARR).1

private theorem rt_of_jitter {sporadic_task : Type u} [DecidableEq sporadic_task] (task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (tsk : sporadic_task) (t1 delta R_tsk : time)
    (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + task_jitter tsk + R_tsk < t1 + delta →
      completed job_cost sched j (job_arrival j + task_jitter tsk + R_tsk) = true) :
    ∀ j : Job, arrives_in arr_seq j → job_task j = tsk → job_arrival j + (task_jitter tsk + R_tsk) < t1 + delta →
      completed job_cost sched j (job_arrival j + (task_jitter tsk + R_tsk)) = true := by
  intro j ARR TSK LT
  rw [← Nat.add_assoc] at LT ⊢
  exact H_response_time_bound j ARR TSK LT

/-! ### Lemmas -/

theorem W_monotonic {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_jitter : sporadic_task → time) (tsk : sporadic_task)
    (H_period_positive : 0 < task_period tsk) (R1 R2 : time) (H_R_lower_bound : task_cost tsk ≤ R1)
    (H_R1_le_R2 : R1 ≤ R2) :
    ∀ t1 t2 : Nat, t1 ≤ t2 →
      W_jitter task_cost task_period task_jitter tsk R1 t1 ≤ W_jitter task_cost task_period task_jitter tsk R2 t2 := by
  intro t1 t2 LEt
  rw [W_jitter_eq, W_jitter_eq]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.W_monotonic task_cost task_period tsk H_period_positive (task_jitter tsk + R1)
    (task_jitter tsk + R2) (Nat.le_trans H_R_lower_bound (Nat.le_add_left _ _)) (Nat.add_le_add_left H_R1_le_R2 _)
    t1 t2 LEt

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

theorem workload_bound_holds_for_at_most_n_k_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (t1 delta R_tsk : time) :
    ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length ≤ max_jobs_jitter task_cost task_period task_jitter tsk R_tsk delta →
    sumSeq ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))) (fun i => service_during sched i t1 (t1 + delta)) ≤
      W_jitter task_cost task_period task_jitter tsk R_tsk delta := by
  rw [max_jobs_jitter_eq, W_jitter_eq]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_holds_for_at_most_n_k_jobs task_cost task_period task_deadline job_arrival job_cost job_task
    job_deadline arr_seq (valid_of_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter arr_seq H_jobs_have_valid_parameters) sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1 delta (task_jitter tsk + R_tsk)

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

theorem workload_bound_holds_for_a_single_job {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched) (tsk : sporadic_task) (t1 delta R_tsk : time) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_at_least_one_job : 0 < ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length)
    (elem : Job) :
    ∑ i ∈ Finset.Ico 0 1, service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD i elem) t1 (t1 + delta) ≤
      W_jitter task_cost task_period task_jitter tsk R_tsk delta := by
  rw [W_jitter_eq]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_holds_for_a_single_job task_cost task_period task_deadline job_arrival job_cost job_task
    job_deadline arr_seq (valid_of_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter arr_seq H_jobs_have_valid_parameters) sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute H_sequential_jobs
    tsk t1 delta (task_jitter tsk + R_tsk) (Nat.le_trans H_response_time_ge_cost (Nat.le_add_left _ _)) H_at_least_one_job elem

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

theorem workload_bound_response_time_of_first_job_inside_interval {sporadic_task : Type u} [DecidableEq sporadic_task] (task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job)
    {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (tsk : sporadic_task) (t1 delta R_tsk : time)
    (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + task_jitter tsk + R_tsk < t1 + delta →
      completed job_cost sched j (job_arrival j + task_jitter tsk + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    t1 ≤ job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) + task_jitter tsk + R_tsk := by
  rw [Nat.add_assoc]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_response_time_of_first_job_inside_interval job_arrival job_cost job_task arr_seq sched
    H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1 delta (task_jitter tsk + R_tsk) (rt_of_jitter task_jitter job_arrival job_cost job_task arr_seq sched tsk t1 delta R_tsk H_response_time_bound) num_mid_jobs
    H_at_least_two_jobs elem

theorem workload_bound_last_job_arrives_before_end_of_interval {sporadic_task : Type u} [DecidableEq sporadic_task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (job_jitter : Job → time) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched) (tsk : sporadic_task) (t1 delta : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) < t1 + delta :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_last_job_arrives_before_end_of_interval job_arrival job_task arr_seq sched
    H_jobs_come_from_arrival_sequence (arrival_before_jitter job_arrival job_jitter sched H_jobs_must_arrive_to_execute) tsk t1 delta num_mid_jobs H_at_least_two_jobs elem

theorem workload_bound_service_of_first_and_last_jobs {sporadic_task : Type u} [DecidableEq sporadic_task] (task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched) (tsk : sporadic_task) (t1 delta R_tsk : time) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + task_jitter tsk + R_tsk < t1 + delta →
      completed job_cost sched j (job_arrival j + task_jitter tsk + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) t1 (t1 + delta) + service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) t1 (t1 + delta) ≤
      (job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) + task_jitter tsk + R_tsk - t1) + (t1 + delta - job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem)) := by
  rw [Nat.add_assoc (job_arrival _)]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_service_of_first_and_last_jobs job_arrival job_cost job_task arr_seq sched
    H_jobs_come_from_arrival_sequence (arrival_before_jitter job_arrival job_jitter sched H_jobs_must_arrive_to_execute) H_completed_jobs_dont_execute H_sequential_jobs tsk t1 delta (task_jitter tsk + R_tsk) (rt_of_jitter task_jitter job_arrival job_cost job_task arr_seq sched tsk t1 delta R_tsk H_response_time_bound)
    num_mid_jobs H_at_least_two_jobs elem

theorem workload_bound_simpl_expression_with_first_and_last {sporadic_task : Type u} [DecidableEq sporadic_task] (task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (t1 delta R_tsk : time) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + task_jitter tsk + R_tsk < t1 + delta →
      completed job_cost sched j (job_arrival j + task_jitter tsk + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) + task_jitter tsk + R_tsk - t1 + (t1 + delta - job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem)) =
      delta + task_jitter tsk + R_tsk - (job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) - job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem)) := by
  rw [Nat.add_assoc (job_arrival _), Nat.add_assoc delta]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_simpl_expression_with_first_and_last job_arrival job_cost job_task arr_seq sched
    H_jobs_come_from_arrival_sequence (arrival_before_jitter job_arrival job_jitter sched H_jobs_must_arrive_to_execute) H_completed_jobs_dont_execute tsk t1 delta (task_jitter tsk + R_tsk) (rt_of_jitter task_jitter job_arrival job_cost job_task arr_seq sched tsk t1 delta R_tsk H_response_time_bound) num_mid_jobs
    H_at_least_two_jobs elem

theorem workload_bound_service_of_middle_jobs {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (tsk : sporadic_task) (t1 delta : time) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    ∑ i ∈ Finset.Ico 0 num_mid_jobs, service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (i + 1) elem) t1 (t1 + delta) ≤
      num_mid_jobs * task_cost tsk :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_service_of_middle_jobs task_cost task_deadline job_arrival job_cost job_task job_deadline arr_seq
    (valid_of_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter arr_seq H_jobs_have_valid_parameters) sched H_jobs_come_from_arrival_sequence H_completed_jobs_dont_execute tsk t1 delta num_mid_jobs
    H_at_least_two_jobs elem

theorem workload_bound_many_periods_in_between {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job] (job_arrival : Job → time)
    (job_task : Job → sporadic_task) (arr_seq : arrival_sequence Job) {num_cpus : Nat}
    (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk) (t1 delta R_tsk : time) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : task_jitter tsk + R_tsk ≤ task_deadline tsk)
    (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    (num_mid_jobs + 1) * task_period tsk ≤ job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) - job_arrival (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) :=
  Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_many_periods_in_between task_cost task_period task_deadline job_arrival job_task arr_seq sched
    H_jobs_come_from_arrival_sequence H_sporadic_tasks tsk H_constrained_deadline t1 delta (task_jitter tsk + R_tsk) (Nat.le_trans H_response_time_ge_cost (Nat.le_add_left _ _))
    H_no_deadline_miss num_mid_jobs H_at_least_two_jobs elem

theorem workload_bound_n_k_covers_middle_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched) (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk) (t1 delta R_tsk : time) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : task_jitter tsk + R_tsk ≤ task_deadline tsk) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + task_jitter tsk + R_tsk < t1 + delta →
      completed job_cost sched j (job_arrival j + task_jitter tsk + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    num_mid_jobs ≤ max_jobs_jitter task_cost task_period task_jitter tsk R_tsk delta := by
  rw [max_jobs_jitter_eq]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_n_k_covers_middle_jobs task_cost task_period task_deadline job_arrival job_cost job_task
    arr_seq sched H_jobs_come_from_arrival_sequence (arrival_before_jitter job_arrival job_jitter sched H_jobs_must_arrive_to_execute) H_completed_jobs_dont_execute H_sporadic_tasks tsk
    H_valid_task_parameters H_constrained_deadline t1 delta (task_jitter tsk + R_tsk) (rt_of_jitter task_jitter job_arrival job_cost job_task arr_seq sched tsk t1 delta R_tsk H_response_time_bound) (Nat.le_trans H_response_time_ge_cost (Nat.le_add_left _ _)) H_no_deadline_miss num_mid_jobs
    H_at_least_two_jobs elem

theorem workload_bound_n_k_equals_num_mid_jobs {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sequential_jobs : sequential_jobs sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk) (t1 delta R_tsk : time) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : task_jitter tsk + R_tsk ≤ task_deadline tsk) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + task_jitter tsk + R_tsk < t1 + delta →
      completed job_cost sched j (job_arrival j + task_jitter tsk + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    num_mid_jobs = max_jobs_jitter task_cost task_period task_jitter tsk R_tsk delta →
    service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) t1 (t1 + delta) + service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) t1 (t1 + delta) +
        ∑ i ∈ Finset.Ico 0 num_mid_jobs, service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (i + 1) elem) t1 (t1 + delta) ≤
      W_jitter task_cost task_period task_jitter tsk R_tsk delta := by
  rw [max_jobs_jitter_eq, W_jitter_eq]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_n_k_equals_num_mid_jobs task_cost task_period task_deadline job_arrival job_cost job_task
    job_deadline arr_seq (valid_of_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter arr_seq H_jobs_have_valid_parameters) sched H_jobs_come_from_arrival_sequence (arrival_before_jitter job_arrival job_jitter sched H_jobs_must_arrive_to_execute) H_completed_jobs_dont_execute
    H_sequential_jobs H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta (task_jitter tsk + R_tsk) (rt_of_jitter task_jitter job_arrival job_cost job_task arr_seq sched tsk t1 delta R_tsk H_response_time_bound) (Nat.le_trans H_response_time_ge_cost (Nat.le_add_left _ _))
    H_no_deadline_miss num_mid_jobs H_at_least_two_jobs elem

theorem workload_bound_n_k_equals_num_mid_jobs_plus_1 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sequential_jobs : sequential_jobs sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk) (t1 delta R_tsk : time) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : task_jitter tsk + R_tsk ≤ task_deadline tsk) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + task_jitter tsk + R_tsk < t1 + delta →
      completed job_cost sched j (job_arrival j + task_jitter tsk + R_tsk) = true) (num_mid_jobs : Nat) (H_at_least_two_jobs : ((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).length = num_mid_jobs + 2) (elem : Job) :
    num_mid_jobs + 1 = max_jobs_jitter task_cost task_period task_jitter tsk R_tsk delta →
    service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (num_mid_jobs + 1) elem) t1 (t1 + delta) + service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD 0 elem) t1 (t1 + delta) +
        ∑ i ∈ Finset.Ico 0 num_mid_jobs, service_during sched (((jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
        (fun x y => decide (job_arrival x ≤ job_arrival y))).getD (i + 1) elem) t1 (t1 + delta) ≤
      W_jitter task_cost task_period task_jitter tsk R_tsk delta := by
  rw [max_jobs_jitter_eq, W_jitter_eq]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bound_n_k_equals_num_mid_jobs_plus_1 task_cost task_period task_deadline job_arrival job_cost
    job_task job_deadline arr_seq (valid_of_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter arr_seq H_jobs_have_valid_parameters) sched H_jobs_come_from_arrival_sequence (arrival_before_jitter job_arrival job_jitter sched H_jobs_must_arrive_to_execute) H_completed_jobs_dont_execute
    H_sequential_jobs H_sporadic_tasks tsk H_constrained_deadline t1 delta (task_jitter tsk + R_tsk) (rt_of_jitter task_jitter job_arrival job_cost job_task arr_seq sched tsk t1 delta R_tsk H_response_time_bound) (Nat.le_trans H_response_time_ge_cost (Nat.le_add_left _ _)) H_no_deadline_miss
    num_mid_jobs H_at_least_two_jobs elem

theorem workload_bounded_by_W {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost : Job → time) (job_task : Job → sporadic_task) (job_deadline job_jitter : Job → time)
    (arr_seq : arrival_sequence Job) (H_jobs_have_valid_parameters : ∀ j : Job, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j) {num_cpus : Nat} (sched : schedule Job num_cpus) (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq) (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched) (H_sequential_jobs : sequential_jobs sched) (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq) (tsk : sporadic_task) (H_valid_task_parameters : is_valid_sporadic_task task_cost task_period task_deadline tsk) (H_constrained_deadline : task_deadline tsk ≤ task_period tsk) (t1 delta R_tsk : time) (H_response_time_ge_cost : task_cost tsk ≤ R_tsk) (H_no_deadline_miss : task_jitter tsk + R_tsk ≤ task_deadline tsk) (H_response_time_bound : ∀ j : Job, arrives_in arr_seq j → job_task j = tsk →
      job_arrival j + task_jitter tsk + R_tsk < t1 + delta →
      completed job_cost sched j (job_arrival j + task_jitter tsk + R_tsk) = true) :
    workload job_task sched tsk t1 (t1 + delta) ≤ W_jitter task_cost task_period task_jitter tsk R_tsk delta := by
  rw [W_jitter_eq]
  exact Prosa.Classic.Analysis.Global.Basic.WorkloadBound.WorkloadBound.workload_bounded_by_W task_cost task_period task_deadline job_arrival job_cost job_task job_deadline arr_seq
    (valid_of_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter arr_seq H_jobs_have_valid_parameters) sched H_jobs_come_from_arrival_sequence (arrival_before_jitter job_arrival job_jitter sched H_jobs_must_arrive_to_execute) H_completed_jobs_dont_execute H_sequential_jobs
    H_sporadic_tasks tsk H_valid_task_parameters H_constrained_deadline t1 delta (task_jitter tsk + R_tsk) (rt_of_jitter task_jitter job_arrival job_cost job_task arr_seq sched tsk t1 delta R_tsk H_response_time_bound) (Nat.le_trans H_response_time_ge_cost (Nat.le_add_left _ _)) H_no_deadline_miss

end Prosa.Classic.Analysis.Global.Jitter.WorkloadBound.WorkloadBoundJitter
