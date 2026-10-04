-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/arrival_curves/workload_bound.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 91)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Arrival.Curves.Bounds

/-!
Request bound functions and workload bounds from arrival curves (Rocq module `MaxArrivalsWorkloadBound`).

Representation notes:
* `\sum_(x <- s | P x) F x` is `sumFiltered s P F`, `\sum_(x <- s) F x` is `sumSeq s F` (v0.6 `Prosa.Util.Sum`);
  `x == y` is `decide (x = y)`, `x != y` is `!decide (x = y)`, `~~ b` is `!b`; `tsk \in ts` is `tsk ∈ ts`.
* The section-local `Let`s (`jlfp_higher_eq_priority`, `arrivals_between`, `is_hep_task`, `is_other_hep_task`,
  `task_rbf`, `total_rbf`, `total_hep_rbf`, `total_ohep_rbf`, `same_task`, `other_higher_eq_priority`,
  `total_workload`, `total_hep_workload`, `total_ohep_workload`, `task_workload`) are unfolded.
* Binder lists follow the Rocq contract (e.g. `task_workload_le_task_rbf` takes `H_tsk_in_ts` and the job `j` with
  `H_job_of_tsk`, but neither `H_all_jobs_from_taskset` nor `H_j_arrives`; `total_workload_le_total_rbf''` takes
  neither `tsk` nor `j`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound.MaxArrivalsWorkloadBound

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Uni.Workload.Workload
open Prosa.Util.Sum (sumFiltered sumSeq leq_sum_seq)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def task_request_bound_function {Task : Type u} [DecidableEq Task] (task_cost : Task → time) (max_arrivals : Task → time → Nat) (tsk : Task)
    (delta : time) : Nat :=
  task_cost tsk * max_arrivals tsk delta

def total_request_bound_function {Task : Type u} [DecidableEq Task] (task_cost : Task → time) (max_arrivals : Task → time → Nat)
    (ts : List Task) (delta : time) : Nat :=
  sumSeq ts (fun tsk => task_request_bound_function task_cost max_arrivals tsk delta)

def total_hep_request_bound_function_FP {Task : Type u} [DecidableEq Task] (task_cost : Task → time) (higher_eq_priority : FP_policy Task)
    (max_arrivals : Task → time → Nat) (ts : List Task) (tsk : Task) (delta : time) : Nat :=
  sumFiltered ts (fun tsk_other => higher_eq_priority tsk_other tsk)
    (fun tsk_other => task_request_bound_function task_cost max_arrivals tsk_other delta)

def total_ohep_request_bound_function_FP {Task : Type u} [DecidableEq Task] (task_cost : Task → time) (higher_eq_priority : FP_policy Task)
    (max_arrivals : Task → time → Nat) (ts : List Task) (tsk : Task) (delta : time) : Nat :=
  sumFiltered ts (fun tsk_other => higher_eq_priority tsk_other tsk && !decide (tsk_other = tsk))
    (fun tsk_other => task_request_bound_function task_cost max_arrivals tsk_other delta)

/-! ### LEAN_HELPER lemmas -/

private theorem le_sumFiltered_of_mem {I : Type _} (r : List I) (P : I → Bool) (F : I → Nat) (x : I)
    (hx : x ∈ r) (hp : P x = true) : F x ≤ sumFiltered r P F := by
  unfold sumFiltered
  exact List.le_sum_of_mem (List.mem_map_of_mem (List.mem_filter.mpr ⟨hx, hp⟩))

/-- LEAN_HELPER: regrouping a workload by task (all jobs come from `ts`). -/
private theorem workload_le_sum_per_task {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (job_task : Job → Task)
    (P : Task → Bool) (ts : List Task) (l : List Job) (FROMTS : ∀ j ∈ l, job_task j ∈ ts) :
    sumFiltered l (fun j => P (job_task j)) job_cost ≤
      sumFiltered ts P (fun tsk' => sumFiltered l (fun j0 => decide (job_task j0 = tsk')) job_cost) := by
  induction l with
  | nil => simp [sumFiltered]
  | cons a l ih =>
    have ih' := ih (fun j hj => FROMTS j (List.mem_cons_of_mem a hj))
    have SPLIT : sumFiltered ts P (fun tsk' => sumFiltered (a :: l) (fun j0 => decide (job_task j0 = tsk')) job_cost) =
        sumFiltered ts P (fun tsk' => if job_task a = tsk' then job_cost a else 0) +
          sumFiltered ts P (fun tsk' => sumFiltered l (fun j0 => decide (job_task j0 = tsk')) job_cost) := by
      unfold sumFiltered
      rw [← List.sum_map_add]
      congr 1
      apply List.map_congr_left
      intro tsk' _
      by_cases h : job_task a = tsk' <;> simp [List.filter_cons, h]
    rw [SPLIT]
    have HEAD : sumFiltered (a :: l) (fun j => P (job_task j)) job_cost =
        (if P (job_task a) = true then job_cost a else 0) + sumFiltered l (fun j => P (job_task j)) job_cost := by
      unfold sumFiltered
      by_cases h : P (job_task a) = true <;> simp [List.filter_cons, h]
    rw [HEAD]
    apply Nat.add_le_add _ ih'
    split
    · next hp =>
      have := le_sumFiltered_of_mem ts P (fun tsk' => if job_task a = tsk' then job_cost a else 0) (job_task a)
        (FROMTS a List.mem_cons_self) hp
      simpa using this
    · exact Nat.zero_le _

/-- LEAN_HELPER: the workload of the jobs of one task is bounded by its request bound function. -/
private theorem per_task_bound {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_cost : Job → time) (job_task : Job → Task)
    (arr_seq : arrival_sequence Job) (ts : List Task) (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true) (max_arrivals : Task → time → Nat) (H_is_arrival_bound : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts)
    (tsk0 : Task) (INtsk0 : tsk0 ∈ ts) (t delta : time) :
    sumFiltered (jobs_arrived_between arr_seq t (t + delta)) (fun j0 => decide (job_task j0 = tsk0)) job_cost ≤
      task_request_bound_function task_cost max_arrivals tsk0 delta := by
  unfold task_request_bound_function
  calc sumFiltered (jobs_arrived_between arr_seq t (t + delta)) (fun j0 => decide (job_task j0 = tsk0)) job_cost
      ≤ num_arrivals_of_task job_task arr_seq tsk0 t (t + delta) * task_cost tsk0 := by
        unfold sumFiltered num_arrivals_of_task arrivals_of_task_between
        have hfilter : (jobs_arrived_between arr_seq t (t + delta)).filter (fun j0 => decide (job_task j0 = tsk0)) = (jobs_arrived_between arr_seq t (t + delta)).filter (is_job_of_task job_task tsk0) :=
          rfl
        rw [hfilter]
        have := List.sum_le_card_nsmul (((jobs_arrived_between arr_seq t (t + delta)).filter (is_job_of_task job_task tsk0)).map job_cost) (task_cost tsk0) (by
          intro x hx
          obtain ⟨j0, hj0, rfl⟩ := List.mem_map.mp hx
          rw [List.mem_filter] at hj0
          have EQ : job_task j0 = tsk0 := by simpa [is_job_of_task] using hj0.2
          have := H_job_cost_le_task_cost j0 (in_arrivals_implies_arrived arr_seq j0 t (t + delta) hj0.1)
          simp only [job_cost_le_task_cost, decide_eq_true_eq, EQ] at this
          exact this)
        simpa [List.length_map] using this
    _ = task_cost tsk0 * num_arrivals_of_task job_task arr_seq tsk0 t (t + delta) := Nat.mul_comm _ _
    _ ≤ task_cost tsk0 * max_arrivals tsk0 delta := by
        apply Nat.mul_le_mul_left
        have := H_is_arrival_bound tsk0 INtsk0 t (t + delta) (Nat.le_add_right _ _)
        rwa [show t + delta - t = delta by omega'] at this

/-! ### Lemmas -/

theorem task_workload_le_task_rbf {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (ts : List Task) (tsk : Task) (H_tsk_in_ts : tsk ∈ ts)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true) (max_arrivals : Task → time → Nat) (H_is_arrival_bound : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts) (j : Job) (H_job_of_tsk : job_task j = tsk) (t delta : time) :
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + delta)) (fun j_other => decide (job_task j_other = job_task j)) ≤
      task_request_bound_function task_cost max_arrivals tsk delta := by
  unfold workload_of_jobs
  rw [H_job_of_tsk]
  exact per_task_bound task_cost job_cost job_task arr_seq ts H_job_cost_le_task_cost max_arrivals
    H_is_arrival_bound tsk H_tsk_in_ts t delta

theorem total_workload_le_total_rbf {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (higher_eq_priority : FP_policy Task)
    (ts : List Task) (tsk : Task) (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true) (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (max_arrivals : Task → time → Nat) (H_is_arrival_bound : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts) (j : Job)
    (H_job_of_tsk : job_task j = tsk) (t delta : time) :
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + delta))
        (fun j_other => FP_to_JLFP job_task higher_eq_priority j_other j && !decide (job_task j_other = job_task j)) ≤
      total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk delta := by
  unfold workload_of_jobs total_ohep_request_bound_function_FP
  simp only [FP_to_JLFP, H_job_of_tsk]
  refine Nat.le_trans (workload_le_sum_per_task job_cost job_task
    (fun tsk' => higher_eq_priority tsk' tsk && !decide (tsk' = tsk)) ts _
    (fun j0 hj0 => H_all_jobs_from_taskset j0 (in_arrivals_implies_arrived arr_seq j0 t (t + delta) hj0))) ?_
  apply leq_sum_seq
  intro tsk0 INtsk0 _
  exact per_task_bound task_cost job_cost job_task arr_seq ts H_job_cost_le_task_cost max_arrivals
    H_is_arrival_bound tsk0 INtsk0 t delta

theorem total_workload_le_total_rbf' {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (higher_eq_priority : FP_policy Task)
    (ts : List Task) (tsk : Task) (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true) (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (max_arrivals : Task → time → Nat) (H_is_arrival_bound : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts) (j : Job)
    (H_job_of_tsk : job_task j = tsk) (t delta : time) :
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + delta)) (fun j_other => FP_to_JLFP job_task higher_eq_priority j_other j) ≤
      total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk delta := by
  unfold workload_of_jobs total_hep_request_bound_function_FP
  simp only [FP_to_JLFP, H_job_of_tsk]
  refine Nat.le_trans (workload_le_sum_per_task job_cost job_task (fun tsk' => higher_eq_priority tsk' tsk) ts _
    (fun j0 hj0 => H_all_jobs_from_taskset j0 (in_arrivals_implies_arrived arr_seq j0 t (t + delta) hj0))) ?_
  apply leq_sum_seq
  intro tsk0 INtsk0 _
  exact per_task_bound task_cost job_cost job_task arr_seq ts H_job_cost_le_task_cost max_arrivals
    H_is_arrival_bound tsk0 INtsk0 t delta

theorem total_workload_le_total_rbf'' {Task : Type u} [DecidableEq Task] (task_cost : Task → time) {Job : Type v} [DecidableEq Job] (job_cost : Job → time)
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (ts : List Task) (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost_le_task_cost task_cost job_cost job_task j = true) (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (max_arrivals : Task → time → Nat) (H_is_arrival_bound : is_arrival_bound_for_taskset job_task arr_seq max_arrivals ts) (t delta : time) :
    workload_of_jobs job_cost (jobs_arrived_between arr_seq t (t + delta)) (fun _ => true) ≤ total_request_bound_function task_cost max_arrivals ts delta := by
  unfold workload_of_jobs total_request_bound_function
  have hseq : sumSeq ts (fun tsk => task_request_bound_function task_cost max_arrivals tsk delta) =
      sumFiltered ts (fun _ => true) (fun tsk => task_request_bound_function task_cost max_arrivals tsk delta) := by
    simp [sumSeq, sumFiltered]
  rw [hseq]
  refine Nat.le_trans (workload_le_sum_per_task job_cost job_task (fun _ => true) ts _
    (fun j0 hj0 => H_all_jobs_from_taskset j0 (in_arrivals_implies_arrived arr_seq j0 t (t + delta) hj0))) ?_
  apply leq_sum_seq
  intro tsk0 INtsk0 _
  exact per_task_bound task_cost job_cost job_task arr_seq ts H_job_cost_le_task_cost max_arrivals
    H_is_arrival_bound tsk0 INtsk0 t delta

end Prosa.Classic.Analysis.Uni.ArrivalCurves.WorkloadBound.MaxArrivalsWorkloadBound
