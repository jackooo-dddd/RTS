-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/parallel/bertogna_edf_theory.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 162)

import Prosa.Util.Sum
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Analysis.Global.Parallel.WorkloadBound
import Prosa.Classic.Analysis.Global.Parallel.InterferenceBoundEdf
import Prosa.Classic.Analysis.Global.Basic.BertognaEdfTheory

/-!
Bertogna and Cirinei's response-time analysis for global EDF scheduling with (potentially) parallel jobs (Rocq
module `ResponseTimeAnalysisEDF` of `classic/analysis/global/parallel/bertogna_edf_theory.v`).

Representation notes (as in the accepted `classic/analysis/global/basic/bertogna_edf_theory.v` translation):
* The section-local `Let`s are unfolded in the statements: `I tsk delta` is the parallel
  `total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta`; `x tsk_other` is
  `task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R)`; `X` is
  `total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R)`; `workload_bound`,
  `edf_specific_bound` and `interference_bound` are the parallel `W …`, `edf_specific_interference_bound … tsk …`
  and `interference_bound_edf … tsk R (tsk_other, R_other)`; `other_task` is `different_task tsk`; `other_tasks` is
  `ts.val.filter (fun tsk_other => different_task tsk tsk_other)`; `response_time_bounded_by` is
  `is_response_time_bound_of_task … sched`.
* `unzip1 rt_bounds = ts` is `rt_bounds.map Prod.fst = ts.val`; `\sum_(i <- s) F i` is `Prosa.Util.Sum.sumSeq s F`
  and `\sum_((tsk_other, R_other) <- s | P) F` is `Prosa.Util.Sum.sumFiltered` with pattern-matching functions.
* Binder lists follow the Rocq contract. `bertogna_edf_interference_on_all_cpus` has the same statement and
  binders as the lemma of the accepted basic translation (it does not involve the parallel bounds) and is proved by
  it; the remaining proofs follow the basic translation with the parallel workload and interference bounds (no
  `H_sequential_jobs`, and no per-task minimum in the interference bound, so lemmas (2)–(4) of the basic analysis
  are not needed, as in the Rocq source).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Parallel.BertognaEdfTheory.ResponseTimeAnalysisEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Workload.Workload
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Basic.Interference.Interference
open Prosa.Classic.Analysis.Global.Parallel.WorkloadBound.WorkloadBound
open Prosa.Classic.Analysis.Global.Parallel.InterferenceBoundEdf.InterferenceBoundEDF
open Prosa.Classic.Util.DivMod (div_floor)
open Prosa.Util.Sum (sumSeq sumFiltered)
open BigOperators

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Lemmas about the interfering tasks -/

/-- LEAN_HELPER: the tasks of the computed list are exactly the tasks of `ts`. -/
private theorem mem_ts_iff_bound {sporadic_task : Type u} [DecidableEq sporadic_task]
    (ts : taskset_of sporadic_task) (rt_bounds : List (sporadic_task × time))
    (H : rt_bounds.map Prod.fst = ts.val) (tsk : sporadic_task) :
    tsk ∈ ts ↔ ∃ R : time, (tsk, R) ∈ rt_bounds := by
  show tsk ∈ ts.val ↔ _
  rw [← H, List.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, rfl⟩
    exact ⟨b, hmem⟩
  · rintro ⟨R, hR⟩
    exact ⟨(tsk, R), hR, rfl⟩

theorem bertogna_edf_tsk_other_in_ts
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (ts : taskset_of sporadic_task)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)
    :
    tsk_other ∈ ts :=
  (mem_ts_iff_bound ts rt_bounds H_rt_bounds_contains_all_tasks tsk_other).mpr
    ⟨R_other, H_response_time_of_tsk_other⟩

theorem bertogna_edf_R_other_ge_cost
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    (num_cpus : Nat)
    (rt_bounds : List (sporadic_task × time))
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds R) num_cpus)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)
    :
    task_cost tsk_other ≤ R_other := by
  have := H_response_time_is_fixed_point tsk_other R_other H_response_time_of_tsk_other
  omega'

theorem bertogna_edf_workload_bounds_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (R : time)
    (j : Job)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + R_other < job_arrival j + R →
        completed job_cost sched j_other (job_arrival j_other + R_other) = true)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)
    :
    task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R) ≤ W task_cost task_period tsk_other R_other R := by
  have INts := bertogna_edf_tsk_other_in_ts ts rt_bounds H_rt_bounds_contains_all_tasks tsk_other
    R_other H_response_time_of_tsk_other
  calc task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R)
      ≤ workload job_task sched tsk_other (job_arrival j) (job_arrival j + R) :=
        task_interference_le_workload job_arrival job_cost job_task sched j tsk_other _ _
    _ ≤ W task_cost task_period tsk_other R_other R :=
        workload_bounded_by_W task_cost task_period task_deadline job_arrival job_cost job_task
          job_deadline arr_seq H_valid_job_parameters sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sporadic_tasks tsk_other
          (H_valid_task_parameters tsk_other INts) (job_arrival j) R R_other
          (fun j' ARR' JOB' LT' => H_all_previous_jobs_completed_on_time j' tsk_other R_other ARR'
            JOB' H_response_time_of_tsk_other LT')

theorem bertogna_edf_specific_bound_holds
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline))
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk_other : sporadic_task) (R : time), (tsk_other, R) ∈ rt_bounds → R ≤ task_deadline tsk_other)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + R_other < job_arrival j + R →
        completed job_cost sched j_other (job_arrival j_other + R_other) = true)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ rt_bounds)
    :
    task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R) ≤ edf_specific_interference_bound task_cost task_period task_deadline tsk tsk_other R_other := by
  have Htsk : tsk ∈ ts :=
    (mem_ts_iff_bound ts rt_bounds H_rt_bounds_contains_all_tasks tsk).mpr ⟨R, H_tsk_R_in_rt_bounds⟩
  have Hother : tsk_other ∈ ts :=
    (mem_ts_iff_bound ts rt_bounds H_rt_bounds_contains_all_tasks tsk_other).mpr
      ⟨R_other, H_response_time_of_tsk_other⟩
  exact interference_bound_edf_bounds_interference task_cost task_period task_deadline job_arrival
    job_cost job_deadline job_task H_sporadic_tasks H_valid_job_parameters num_cpus sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_at_least_one_cpu ts H_valid_task_parameters H_constrained_deadlines H_edf_policy tsk Htsk j H_j_arrives
    H_job_of_tsk tsk_other Hother R_other (H_tasks_miss_no_deadlines _ _ H_response_time_of_tsk_other) R
    (H_tasks_miss_no_deadlines _ _ H_tsk_R_in_rt_bounds)
    (fun j_k ARR JOB LT => H_all_previous_jobs_completed_on_time j_k tsk_other R_other ARR JOB
      H_response_time_of_tsk_other LT)

/-! ### Deriving a contradiction -/

theorem bertogna_edf_too_much_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (rt_bounds : List (sporadic_task × time))
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds R) num_cpus)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    :
    R - task_cost tsk + 1 ≤ total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) := by
  have hRe : task_cost tsk ≤ R := by
    have := H_response_time_is_fixed_point tsk R H_tsk_R_in_rt_bounds
    omega'
  have NOTCOMP := H_j_not_completed
  simp only [completed, Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_le] at NOTCOMP
  have hcost : job_cost j ≤ task_cost tsk := by
    have := (H_valid_job_parameters j H_j_arrives).2.1
    simp only [job_cost_le_task_cost, decide_eq_true_eq] at this
    rw [H_job_of_tsk] at this
    exact this
  have hsvc : service sched j (job_arrival j + R) =
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), service_at sched j t :=
    service_before_arrival_eq_service_during job_arrival sched j H_jobs_must_arrive_to_execute 0 R
      (Nat.zero_le _)
  have hcover : R ≤ ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      ((backlogged job_arrival job_cost sched j t).toNat + service_at sched j t) := by
    calc R = ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), 1 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro t ht
        rw [Finset.mem_Ico] at ht
        cases hb : backlogged job_arrival job_cost sched j t
        · simp only [Bool.toNat_false, Nat.zero_add]
          have hpend : pending job_arrival job_cost sched j t = true := by
            simp only [pending, has_arrived, Bool.and_eq_true, decide_eq_true_eq,
              Bool.not_eq_true']
            refine ⟨ht.1, ?_⟩
            cases hc : completed job_cost sched j t
            · rfl
            · have := completion_monotonic job_cost sched j t (job_arrival j + R)
                (Nat.le_of_lt ht.2) hc
              simp only [completed, decide_eq_true_eq] at this
              omega'
          simp only [backlogged, hpend, Bool.true_and, Bool.not_eq_false'] at hb
          have := not_scheduled_no_service sched j t
          rw [hb] at this
          have hne : service_at sched j t ≠ 0 := by
            intro h0; rw [h0] at this; simp at this
          omega'
        · simp
  unfold total_interference
  rw [Finset.sum_add_distrib] at hcover
  rw [hsvc] at NOTCOMP
  omega'

theorem bertogna_edf_interference_on_all_cpus
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk_other : sporadic_task) (R : time), (tsk_other, R) ∈ rt_bounds → R ≤ task_deadline tsk_other)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + R_other < job_arrival j + R →
        completed job_cost sched j_other (job_arrival j_other + R_other) = true)
    :
    sumSeq (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) = total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) * num_cpus :=
  Prosa.Classic.Analysis.Global.Basic.BertognaEdfTheory.ResponseTimeAnalysisEDF.bertogna_edf_interference_on_all_cpus
    task_cost task_period task_deadline job_arrival job_cost job_task arr_seq H_sporadic_tasks ts
    H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    H_work_conserving rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk R
    H_tsk_R_in_rt_bounds j H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time

theorem bertogna_edf_sum_exceeds_total_interference
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds R) num_cpus)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk_other : sporadic_task) (R : time), (tsk_other, R) ∈ rt_bounds → R ≤ task_deadline tsk_other)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + R_other < job_arrival j + R →
        completed job_cost sched j_other (job_arrival j_other + R_other) = true)
    :
    total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds R <
      sumFiltered rt_bounds (fun (tsk_other, _) => different_task tsk tsk_other)
        (fun (tsk_other, _) => task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R)) := by
  have ALLBUSY := bertogna_edf_interference_on_all_cpus task_cost task_period task_deadline job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk R H_tsk_R_in_rt_bounds j H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time
  have TOOMUCH := bertogna_edf_too_much_interference task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_valid_job_parameters num_cpus sched H_jobs_must_arrive_to_execute rt_bounds H_response_time_is_fixed_point tsk R H_tsk_R_in_rt_bounds j H_j_arrives H_job_of_tsk H_j_not_completed
  have hsub : sumSeq (ts.val.filter (fun tsk_other => different_task tsk tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) =
      sumFiltered rt_bounds (fun (tsk_other, _) => different_task tsk tsk_other)
        (fun (tsk_other, _) => task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R)) := by
    unfold sumSeq sumFiltered
    rw [← H_rt_bounds_contains_all_tasks, List.filter_map, List.map_map]
    rfl
  rw [← hsub, ALLBUSY]
  have REC := H_response_time_is_fixed_point tsk R H_tsk_R_in_rt_bounds
  unfold div_floor at REC
  by_contra NOT
  have LE := Nat.le_of_not_lt NOT
  have STEP : (R - task_cost tsk + 1) * num_cpus ≤
      total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds R :=
    Nat.le_trans (Nat.mul_le_mul_right _ TOOMUCH) LE
  have := (Nat.le_div_iff_mul_le H_at_least_one_cpu).mpr STEP
  omega'

theorem bertogna_edf_exists_task_that_exceeds_bound
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline))
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds R) num_cpus)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk_other : sporadic_task) (R : time), (tsk_other, R) ∈ rt_bounds → R ≤ task_deadline tsk_other)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_all_previous_jobs_completed_on_time :
      ∀ (j_other : Job) (tsk_other : sporadic_task) (R_other : time),
        arrives_in arr_seq j_other → job_task j_other = tsk_other →
        (tsk_other, R_other) ∈ rt_bounds →
        job_arrival j_other + R_other < job_arrival j + R →
        completed job_cost sched j_other (job_arrival j_other + R_other) = true)
    :
    ∃ (tsk_other : sporadic_task) (R_other : time),
      (tsk_other, R_other) ∈ rt_bounds ∧
      interference_bound_edf task_cost task_period task_deadline tsk R (tsk_other, R_other) < task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R) := by
  have SUM := bertogna_edf_sum_exceeds_total_interference task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving rt_bounds H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines tsk R H_tsk_R_in_rt_bounds j H_j_arrives H_job_of_tsk H_j_not_completed H_all_previous_jobs_completed_on_time
  by_contra NOT
  simp only [not_exists, not_and, Nat.not_lt] at NOT
  apply absurd SUM
  apply Nat.not_lt.mpr
  unfold total_interference_bound_edf sumFiltered
  apply List.sum_le_sum
  rintro ⟨k, Rk⟩ hk
  rw [List.mem_filter] at hk
  exact NOT k Rk hk.1

/-! ### Main theorem -/

theorem bertogna_cirinei_response_time_bound_edf
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → time)
    (task_period : sporadic_task → time)
    (task_deadline : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_cost : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → sporadic_task)
    (arr_seq : arrival_sequence Job)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_valid_job_parameters :
      ∀ j : Job, arrives_in arr_seq j →
        valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters :
      valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines :
      ∀ tsk : sporadic_task, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost arr_seq sched (EDF job_arrival job_deadline))
    (rt_bounds : List (sporadic_task × time))
    (H_rt_bounds_contains_all_tasks : rt_bounds.map Prod.fst = ts.val)
    (H_response_time_is_fixed_point :
      ∀ (tsk : sporadic_task) (R : time), (tsk, R) ∈ rt_bounds →
        R = task_cost tsk +
          div_floor (total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds R) num_cpus)
    (H_tasks_miss_no_deadlines :
      ∀ (tsk_other : sporadic_task) (R : time), (tsk_other, R) ∈ rt_bounds → R ≤ task_deadline tsk_other)
    (tsk : sporadic_task)
    (R : time)
    (H_tsk_R_in_rt_bounds : (tsk, R) ∈ rt_bounds)
    :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  suffices MAIN : ∀ (n : Nat) (j : Job) (tsk : sporadic_task) (R : time),
      job_arrival j + R = n → (tsk, R) ∈ rt_bounds → arrives_in arr_seq j → job_task j = tsk →
      completed job_cost sched j (job_arrival j + R) = true by
    intro j ARRj JOBtsk
    exact MAIN _ j tsk R rfl H_tsk_R_in_rt_bounds ARRj JOBtsk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j tsk' R' hn INbounds ARRj JOBtsk
    by_contra NOTCOMP
    have NOTCOMP' : (!completed job_cost sched j (job_arrival j + R')) = true := by
      simpa using NOTCOMP
    have BEFOREok : ∀ (j0 : Job) (tsk0 : sporadic_task) (R0 : time),
        arrives_in arr_seq j0 → job_task j0 = tsk0 → (tsk0, R0) ∈ rt_bounds →
        job_arrival j0 + R0 < job_arrival j + R' →
        completed job_cost sched j0 (job_arrival j0 + R0) = true :=
      fun j0 tsk0 R0 ARR0 JOB0 IN0 LT0 => IH _ (hn ▸ LT0) j0 tsk0 R0 rfl IN0 ARR0 JOB0
    obtain ⟨tsk_other, R_other, HP, LTmin⟩ := bertogna_edf_exists_task_that_exceeds_bound task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_work_conserving H_edf_policy rt_bounds H_rt_bounds_contains_all_tasks H_response_time_is_fixed_point H_tasks_miss_no_deadlines tsk' R' INbounds j ARRj JOBtsk NOTCOMP' BEFOREok
    have BASIC := bertogna_edf_workload_bounds_interference task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute rt_bounds H_rt_bounds_contains_all_tasks R' j BEFOREok tsk_other R_other HP
    have EDFB := bertogna_edf_specific_bound_holds task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu H_edf_policy rt_bounds H_rt_bounds_contains_all_tasks H_tasks_miss_no_deadlines tsk' R' INbounds j ARRj JOBtsk BEFOREok tsk_other R_other HP
    simp only [interference_bound_edf, interference_bound_generic] at LTmin
    exact absurd LTmin (Nat.not_lt.mpr (le_min BASIC EDFB))

end Prosa.Classic.Analysis.Global.Parallel.BertognaEdfTheory.ResponseTimeAnalysisEDF
