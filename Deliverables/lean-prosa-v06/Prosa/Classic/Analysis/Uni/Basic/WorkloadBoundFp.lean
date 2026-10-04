-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/basic/workload_bound_fp.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 74)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Arrival.Basic.ArrivalBounds
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Workload

/-!
Workload bound for uniprocessor FP scheduling (Rocq module `WorkloadBoundFP`).

Representation notes:
* `\sum_(x <- s | P x) F x` is `sumFiltered s P F` (v0.6 `Prosa.Util.Sum`); `tsk \in ts` is `tsk ∈ ts`.
* `div_ceil` is the classic `Prosa.Classic.Util.DivMod.div_ceil`.
* The section-local `Let`s (`is_hep_task`, `W`, `workload_bound`, `arrivals_between`, `hp_workload`) are unfolded.
* Binder lists follow the Rocq contract (e.g. `total_workload_bound_fp_non_decreasing` and
  `fp_workload_bound_holds` do not take `H_tsk_in_ts`).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Basic.WorkloadBoundFp.WorkloadBoundFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Arrival.Basic.ArrivalBounds.ArrivalBounds
open Prosa.Classic.Model.Schedule.Uni.Workload.Workload
open Prosa.Classic.Util.DivMod (div_ceil ceil_neq0 leq_divceil2r)
open Prosa.Util.Sum (sumFiltered leq_sum_seq)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def max_jobs {Task : Type u} [DecidableEq Task] (task_period : Task → time) (tsk : Task) (delta : time) : Nat :=
  div_ceil delta (task_period tsk)

def task_workload_bound_FP {Task : Type u} [DecidableEq Task] (task_cost task_period : Task → time) (tsk : Task)
    (delta : time) : Nat :=
  max_jobs task_period tsk delta * task_cost tsk

def total_workload_bound_fp {Task : Type u} [DecidableEq Task] (task_cost task_period : Task → time)
    (higher_eq_priority : FP_policy Task) (ts : List Task) (tsk : Task) (delta : time) : Nat :=
  sumFiltered ts (fun tsk_other => higher_eq_priority tsk_other tsk)
    (fun tsk_other => task_workload_bound_FP task_cost task_period tsk_other delta)

/-- LEAN_HELPER: a retained term is bounded by the filtered sum. -/
private theorem le_sumFiltered_of_mem {I : Type _} (r : List I) (P : I → Bool) (F : I → Nat) (x : I)
    (hx : x ∈ r) (hp : P x = true) : F x ≤ sumFiltered r P F := by
  unfold sumFiltered
  exact List.le_sum_of_mem (List.mem_map_of_mem (List.mem_filter.mpr ⟨hx, hp⟩))

theorem total_workload_bound_fp_ge_cost {Task : Type u} [DecidableEq Task] (task_cost task_period : Task → time)
    (higher_eq_priority : FP_policy Task) (ts : List Task) (tsk : Task) (H_tsk_in_ts : tsk ∈ ts)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority) (H_cost_positive : 0 < task_cost tsk)
    (H_period_positive : 0 < task_period tsk) :
    task_cost tsk ≤ total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk (task_cost tsk) := by
  unfold total_workload_bound_fp
  refine Nat.le_trans ?_ (le_sumFiltered_of_mem ts _ _ tsk H_tsk_in_ts (H_priority_is_reflexive tsk))
  unfold task_workload_bound_FP max_jobs
  have := ceil_neq0 (task_cost tsk) (task_period tsk) H_cost_positive H_period_positive
  calc task_cost tsk = 1 * task_cost tsk := (Nat.one_mul _).symm
    _ ≤ _ := Nat.mul_le_mul_right _ this

theorem total_workload_bound_fp_non_decreasing {Task : Type u} [DecidableEq Task]
    (task_cost task_period : Task → time) (higher_eq_priority : FP_policy Task) (ts : List Task) (tsk : Task)
    (H_period_positive : ∀ tsk, tsk ∈ ts → 0 < task_period tsk) :
    ∀ delta1 delta2 : Nat, delta1 ≤ delta2 →
      total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk delta1 ≤
        total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk delta2 := by
  intro d1 d2 LE
  unfold total_workload_bound_fp
  apply leq_sum_seq
  intro tsk' IN _
  unfold task_workload_bound_FP max_jobs
  exact Nat.mul_le_mul_right _ (leq_divceil2r _ _ _ (H_period_positive tsk' IN) LE)

/-- LEAN_HELPER: regrouping the higher-or-equal-priority workload by task. -/
private theorem workload_le_sum_per_task {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_cost : Job → time) (job_task : Job → Task) (P : Task → Bool) (ts : List Task) (l : List Job)
    (FROMTS : ∀ j ∈ l, job_task j ∈ ts) :
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

theorem fp_workload_bound_holds {Task : Type u} [DecidableEq Task] (task_cost task_period task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time) (job_task : Job → Task)
    (ts : List Task) (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (tsk : Task) (higher_eq_priority : FP_policy Task) (R : time)
    (H_fixed_point : R = total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk R) :
    ∀ t : time,
      workload_of_higher_or_equal_priority_tasks job_cost job_task (jobs_arrived_between arr_seq t (t + R))
        higher_eq_priority tsk ≤ R := by
  intro t
  unfold workload_of_higher_or_equal_priority_tasks workload_of_jobs
  have FROMTS : ∀ j ∈ jobs_arrived_between arr_seq t (t + R), job_task j ∈ ts := fun j hj =>
    H_all_jobs_from_taskset j (in_arrivals_implies_arrived arr_seq j t (t + R) hj)
  refine Nat.le_trans (workload_le_sum_per_task job_cost job_task (fun tsk' => higher_eq_priority tsk' tsk) ts _
    FROMTS) ?_
  conv => rhs; rw [H_fixed_point]
  unfold total_workload_bound_fp
  apply leq_sum_seq
  intro tsk0 INtsk0 _
  have PER : 0 < task_period tsk0 := by
    have := (H_valid_task_parameters tsk0 INtsk0).2.1
    simpa [task_period_positive] using this
  calc sumFiltered (jobs_arrived_between arr_seq t (t + R)) (fun j0 => decide (job_task j0 = tsk0)) job_cost
      ≤ num_arrivals_of_task job_task arr_seq tsk0 t (t + R) * task_cost tsk0 := by
        unfold sumFiltered num_arrivals_of_task arrivals_of_task_between
        have hfilter : (jobs_arrived_between arr_seq t (t + R)).filter (fun j0 => decide (job_task j0 = tsk0)) =
            (jobs_arrived_between arr_seq t (t + R)).filter (is_job_of_task job_task tsk0) := rfl
        rw [hfilter]
        have := List.sum_le_card_nsmul
          (((jobs_arrived_between arr_seq t (t + R)).filter (is_job_of_task job_task tsk0)).map job_cost)
          (task_cost tsk0) (by
            intro x hx
            obtain ⟨j0, hj0, rfl⟩ := List.mem_map.mp hx
            rw [List.mem_filter] at hj0
            have EQ : job_task j0 = tsk0 := by simpa [is_job_of_task] using hj0.2
            have := (H_valid_job_parameters j0 (in_arrivals_implies_arrived arr_seq j0 t (t + R) hj0.1)).2.1
            simp only [job_cost_le_task_cost, decide_eq_true_eq, EQ] at this
            exact this)
        simpa [List.length_map] using this
    _ ≤ task_workload_bound_FP task_cost task_period tsk0 R := by
        unfold task_workload_bound_FP max_jobs
        apply Nat.mul_le_mul_right
        have BOUND := sporadic_task_arrival_bound task_period job_arrival job_task arr_seq
          H_arrival_times_are_consistent H_arr_seq_is_a_set H_sporadic_arrivals t (t + R) tsk0 PER
        rwa [show t + R - t = R by omega'] at BOUND

end Prosa.Classic.Analysis.Uni.Basic.WorkloadBoundFp.WorkloadBoundFP
