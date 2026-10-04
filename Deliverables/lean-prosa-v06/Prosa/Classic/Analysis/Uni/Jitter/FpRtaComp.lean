-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/jitter/fp_rta_comp.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 130)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence
import Prosa.Classic.Model.Arrival.Jitter.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Analysis.Uni.Jitter.WorkloadBoundFp
import Prosa.Classic.Analysis.Uni.Jitter.FpRtaTheory

/-!
Fixed-point iteration for jitter-aware uniprocessor FP response-time analysis (Rocq module `ResponseTimeIterationFP`
of `classic/analysis/uni/jitter/fp_rta_comp.v`).

Representation notes:
* `task_with_response_time := (SporadicTask * time)%type` is `SporadicTask × time`; `[seq f x | x <- s]` is
  `s.map f`; `pmap f s` is `s.filterMap f`; MathComp's `all p s` over an `option`-valued `p` (coerced to `bool`) is
  `s.all (fun x => (p x).isSome)`; `if o is (a, Some b) then … else …` is a `match`; `o != None` is
  `!decide (o = none)`; `x \In A` is the accepted classic `optIn x A` (as `= true`).
* The section-local `Let is_valid_bound` (used twice by `fp_claimed_bounds`) is kept as the `LEAN_HELPER` definition
  `is_valid_bound`; the other `Let`s (`task_with_response_time`, `workload_bound`, `no_deadline_missed_by_task`,
  `no_deadline_missed_by_job`, `response_time_bounded_by`, `RTA_claimed_bounds`, `claimed_to_be_schedulable`) are
  unfolded.
* Binder lists follow the Rocq contract.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Jitter.FpRtaComp.ResponseTimeIterationFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival (sporadic_task_model)
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule hiding pending backlogged scheduled_implies_pending
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability
open Prosa.Classic.Analysis.Uni.Jitter.WorkloadBoundFp.WorkloadBoundFP
open Prosa.Classic.Analysis.Uni.Jitter.FpRtaTheory.ResponseTimeAnalysisFP
open Prosa.Classic.Util.Fixedpoint (iter_fixpoint iter_fixpoint_cases iter_fixpoint_ge_bottom)
open Prosa.Classic.Util.Notation (optIn)

universe u v

def max_steps {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_deadline : SporadicTask → time) (tsk : SporadicTask) : Nat :=
  task_deadline tsk - task_cost tsk + 1

def per_task_rta {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask)
    (tsk : SporadicTask) : Option Nat :=
  iter_fixpoint (total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk)
    (max_steps task_cost task_deadline tsk) (task_cost tsk)

/-- LEAN_HELPER (Rocq `Let is_valid_bound`). -/
def is_valid_bound {SporadicTask : Type u} [DecidableEq SporadicTask] (task_deadline task_jitter : SporadicTask → time) (tsk_R : SporadicTask × Option Nat) :
    Option (SporadicTask × time) :=
  match tsk_R with
  | (tsk, some R) => if task_jitter tsk + R ≤ task_deadline tsk then some (tsk, R) else none
  | (_, none) => none

def fp_claimed_bounds {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask) :
    Option (List (SporadicTask × time)) :=
  let possible_bounds := ts.map (fun tsk => (tsk, per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk))
  if possible_bounds.all (fun p => (is_valid_bound task_deadline task_jitter p).isSome) then
    some (possible_bounds.filterMap (is_valid_bound task_deadline task_jitter))
  else none

def fp_schedulable {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask) : Bool :=
  !decide (fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = none)

/-! ### Properties of the computed bounds -/

/-- LEAN_HELPER: the computed list consists of the validated per-task results. -/
private theorem mem_rt_bounds {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask)
    (rt_bounds : List (SporadicTask × time)) (H_analysis_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = some rt_bounds) (tsk : SporadicTask) (R : time) :
    (tsk, R) ∈ rt_bounds ↔ tsk ∈ ts ∧ per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk = some R ∧ task_jitter tsk + R ≤ task_deadline tsk := by
  unfold fp_claimed_bounds at H_analysis_succeeds
  simp only at H_analysis_succeeds
  split at H_analysis_succeeds
  · rw [← Option.some.inj H_analysis_succeeds, List.mem_filterMap]
    constructor
    · rintro ⟨p, hp, hv⟩
      obtain ⟨tsk', IN, rfl⟩ := List.mem_map.mp hp
      unfold is_valid_bound at hv
      split at hv
      · next t0 R0 heq =>
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, hR⟩ := heq
        split at hv
        · next hle =>
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hv)
          exact ⟨IN, hR, hle⟩
        · exact absurd hv (by simp)
      · exact absurd hv (by simp)
    · rintro ⟨IN, hR, hle⟩
      refine ⟨(tsk, per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk), List.mem_map_of_mem IN, ?_⟩
      simp [is_valid_bound, hR, hle]
  · exact absurd H_analysis_succeeds (by simp)

theorem fp_claimed_bounds_for_every_task {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask)
    (rt_bounds : List (SporadicTask × time)) (H_analysis_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = some rt_bounds) (tsk : SporadicTask) (H_tsk_in_ts : tsk ∈ ts) :
    ∃ R, (tsk, R) ∈ rt_bounds := by
  have SOME := H_analysis_succeeds
  unfold fp_claimed_bounds at SOME
  simp only at SOME
  split at SOME
  · next ALL =>
    rw [List.all_eq_true] at ALL
    have V := ALL (tsk, per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk) (List.mem_map_of_mem H_tsk_in_ts)
    cases hR : per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk with
    | none => rw [hR] at V; simp [is_valid_bound] at V
    | some R =>
      refine ⟨R, (mem_rt_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R).mpr ⟨H_tsk_in_ts, hR, ?_⟩⟩
      rw [hR] at V
      simp only [is_valid_bound] at V
      split at V
      · assumption
      · simp at V
  · exact absurd SOME (by simp)

theorem fp_claimed_bounds_from_taskset {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask)
    (rt_bounds : List (SporadicTask × time)) (H_analysis_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = some rt_bounds) (tsk : SporadicTask) (R : time)
    (H_tsk_R_computed : (tsk, R) ∈ rt_bounds) : tsk ∈ ts :=
  ((mem_rt_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R).mp H_tsk_R_computed).1

theorem fp_claimed_bounds_computes_iteration {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask)
    (rt_bounds : List (SporadicTask × time)) (H_analysis_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = some rt_bounds) (tsk : SporadicTask) (R : time)
    (H_tsk_R_computed : (tsk, R) ∈ rt_bounds) : per_task_rta task_cost task_period task_deadline task_jitter higher_eq_priority ts tsk = some R :=
  ((mem_rt_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R).mp H_tsk_R_computed).2.1

theorem fp_claimed_bounds_yields_fixed_point {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask)
    (rt_bounds : List (SporadicTask × time)) (H_analysis_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = some rt_bounds) (tsk : SporadicTask) (R : time)
    (H_tsk_R_computed : (tsk, R) ∈ rt_bounds) :
    R = total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk R := by
  have ITER := fp_claimed_bounds_computes_iteration task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
  unfold per_task_rta at ITER
  rcases iter_fixpoint_cases (total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk)
      (max_steps task_cost task_deadline tsk) (task_cost tsk) with NONE | ⟨R', SOME, EQ⟩
  · rw [NONE] at ITER; exact absurd ITER (by simp)
  · rw [SOME] at ITER
    rw [← Option.some.inj ITER]; exact EQ

theorem fp_claimed_bounds_le_deadline {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask)
    (rt_bounds : List (SporadicTask × time)) (H_analysis_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = some rt_bounds) (tsk : SporadicTask) (R : time)
    (H_tsk_R_computed : (tsk, R) ∈ rt_bounds) : task_jitter tsk + R ≤ task_deadline tsk :=
  ((mem_rt_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R).mp H_tsk_R_computed).2.2

theorem fp_claimed_bounds_ge_cost {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask)
    (rt_bounds : List (SporadicTask × time)) (H_analysis_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = some rt_bounds) (tsk : SporadicTask) (R : time) (H_tsk_R_computed : (tsk, R) ∈ rt_bounds)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority) (H_cost_positive : 0 < task_cost tsk)
    (H_period_positive : ∀ tsk, tsk ∈ ts → 0 < task_period tsk) :
    task_cost tsk ≤ R := by
  have ITER := fp_claimed_bounds_computes_iteration task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
  have IN := fp_claimed_bounds_from_taskset task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
  unfold per_task_rta at ITER
  have GE := total_workload_bound_fp_ge_cost task_cost task_period task_jitter higher_eq_priority ts tsk IN
    H_priority_is_reflexive H_cost_positive (H_period_positive tsk IN)
  have := iter_fixpoint_ge_bottom (total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk)
    (fun a b => decide (a ≤ b)) (fun x => by simp) (fun y x z h1 h2 => decide_eq_true (Nat.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2)))
    (fun x y h => by
      simp only [decide_eq_true_eq] at h ⊢
      exact total_workload_bound_fp_non_decreasing task_cost task_period task_jitter higher_eq_priority ts tsk
        H_period_positive x y h)
    (max_steps task_cost task_deadline tsk) (task_cost tsk) R ITER (by simpa using GE)
  simpa using this

theorem fp_claimed_bounds_gt_zero {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) (higher_eq_priority : FP_policy SporadicTask) (ts : List SporadicTask)
    (rt_bounds : List (SporadicTask × time)) (H_analysis_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts = some rt_bounds) (tsk : SporadicTask) (R : time) (H_tsk_R_computed : (tsk, R) ∈ rt_bounds)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority) (H_cost_positive : 0 < task_cost tsk)
    (H_period_positive : ∀ tsk, tsk ∈ ts → 0 < task_period tsk) : 0 < R :=
  Nat.lt_of_lt_of_le H_cost_positive
    (fp_claimed_bounds_ge_cost task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed H_priority_is_reflexive H_cost_positive
      H_period_positive)

/-! ### Correctness of the analysis -/

theorem fp_analysis_yields_response_time_bounds {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (job_task : Job → SporadicTask) (ts : List SporadicTask)
    (H_positive_costs : ∀ tsk, tsk ∈ ts → 0 < task_cost tsk)
    (H_positive_periods : ∀ tsk, tsk ∈ ts → 0 < task_period tsk) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))
    (H_job_jitter_le_task_jitter : ∀ j, arrives_in arr_seq j → job_jitter j ≤ task_jitter (job_task j))
    (higher_eq_priority : FP_policy SporadicTask) (H_priority_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_transitive : FP_is_transitive higher_eq_priority) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_jitter job_task arr_seq sched higher_eq_priority) :
    ∀ (tsk : SporadicTask) (R : time),
      optIn (tsk, R) (fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts) = true →
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
  intro tsk R IN
  cases SOME : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts with
  | none => rw [SOME] at IN; simp [optIn] at IN
  | some rt_bounds =>
    rw [SOME] at IN
    simp only [optIn, decide_eq_true_eq] at IN
    have INts := fp_claimed_bounds_from_taskset task_cost task_period task_deadline task_jitter higher_eq_priority ts
      rt_bounds SOME tsk R IN
    exact uniprocessor_response_time_bound_fp task_cost task_period task_jitter job_arrival job_cost job_jitter job_task
      ts H_positive_periods arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set H_sporadic_tasks
      H_job_cost_le_task_cost H_job_jitter_le_task_jitter H_all_jobs_from_taskset sched
      H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute higher_eq_priority
      H_priority_reflexive H_priority_transitive H_work_conserving H_respects_FP_policy tsk R
      (fp_claimed_bounds_gt_zero task_cost task_period task_deadline task_jitter higher_eq_priority ts rt_bounds SOME
        tsk R IN H_priority_reflexive (H_positive_costs tsk INts) H_positive_periods)
      (fp_claimed_bounds_yields_fixed_point task_cost task_period task_deadline task_jitter higher_eq_priority ts
        rt_bounds SOME tsk R IN)

theorem taskset_schedulable_by_fp_rta {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline job_jitter : Job → time) (job_task : Job → SporadicTask)
    (ts : List SporadicTask)
    (H_positive_costs : ∀ tsk, tsk ∈ ts → 0 < task_cost tsk)
    (H_positive_periods : ∀ tsk, tsk ∈ ts → 0 < task_period tsk) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))
    (H_job_jitter_le_task_jitter : ∀ j, arrives_in arr_seq j → job_jitter j ≤ task_jitter (job_task j))
    (H_job_deadline_eq_task_deadline : ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (higher_eq_priority : FP_policy SporadicTask) (H_priority_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_transitive : FP_is_transitive higher_eq_priority) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_jitter job_task arr_seq sched higher_eq_priority)
    (H_test_succeeds : fp_schedulable task_cost task_period task_deadline task_jitter higher_eq_priority ts = true) :
    ∀ tsk, tsk ∈ ts → task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  intro tsk IN
  unfold fp_schedulable at H_test_succeeds
  cases TEST : fp_claimed_bounds task_cost task_period task_deadline task_jitter higher_eq_priority ts with
  | none => rw [TEST] at H_test_succeeds; simp at H_test_succeeds
  | some rt_bounds =>
    obtain ⟨R, INbounds⟩ := fp_claimed_bounds_for_every_task task_cost task_period task_deadline task_jitter
      higher_eq_priority ts rt_bounds TEST tsk IN
    have DL := fp_claimed_bounds_le_deadline task_cost task_period task_deadline task_jitter higher_eq_priority ts
      rt_bounds TEST tsk R INbounds
    exact task_completes_before_deadline job_arrival job_cost job_deadline job_task arr_seq sched task_deadline
      H_job_deadline_eq_task_deadline tsk (task_jitter tsk + R) DL
      (fp_analysis_yields_response_time_bounds task_cost task_period task_deadline task_jitter job_arrival job_cost
        job_jitter job_task ts H_positive_costs H_positive_periods arr_seq H_arrival_times_are_consistent
        H_arr_seq_is_a_set H_all_jobs_from_taskset H_sporadic_tasks H_job_cost_le_task_cost
        H_job_jitter_le_task_jitter higher_eq_priority H_priority_reflexive H_priority_transitive sched
        H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving
        H_respects_FP_policy tsk R (by rw [TEST]; simp [optIn, INbounds]))

theorem jobs_schedulable_by_fp_rta {SporadicTask : Type u} [DecidableEq SporadicTask] (task_cost task_period task_deadline task_jitter : SporadicTask → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline job_jitter : Job → time) (job_task : Job → SporadicTask)
    (ts : List SporadicTask)
    (H_positive_costs : ∀ tsk, tsk ∈ ts → 0 < task_cost tsk)
    (H_positive_periods : ∀ tsk, tsk ∈ ts → 0 < task_period tsk) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))
    (H_job_jitter_le_task_jitter : ∀ j, arrives_in arr_seq j → job_jitter j ≤ task_jitter (job_task j))
    (H_job_deadline_eq_task_deadline : ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (higher_eq_priority : FP_policy SporadicTask) (H_priority_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_transitive : FP_is_transitive higher_eq_priority) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_FP_policy : respects_FP_policy job_arrival job_cost job_jitter job_task arr_seq sched higher_eq_priority)
    (H_test_succeeds : fp_schedulable task_cost task_period task_deadline task_jitter higher_eq_priority ts = true) :
    ∀ j, arrives_in arr_seq j → job_misses_no_deadline job_arrival job_cost job_deadline sched j := by
  intro j ARRj
  exact taskset_schedulable_by_fp_rta task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline
    job_jitter job_task ts H_positive_costs H_positive_periods arr_seq H_arrival_times_are_consistent
    H_arr_seq_is_a_set H_all_jobs_from_taskset H_sporadic_tasks H_job_cost_le_task_cost H_job_jitter_le_task_jitter
    H_job_deadline_eq_task_deadline higher_eq_priority H_priority_reflexive H_priority_transitive sched
    H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_work_conserving
    H_respects_FP_policy H_test_succeeds (job_task j) (H_all_jobs_from_taskset j ARRj) j ARRj rfl

end Prosa.Classic.Analysis.Uni.Jitter.FpRtaComp.ResponseTimeIterationFP
