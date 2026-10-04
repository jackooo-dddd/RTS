-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/parallel/bertogna_fp_theory.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 146)

import Prosa.Util.Sum
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.ResponseTime
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Schedule.Global.Basic.ConstrainedDeadlines
import Prosa.Classic.Model.Schedule.Global.Basic.Interference
import Prosa.Classic.Analysis.Global.Parallel.WorkloadBound
import Prosa.Classic.Analysis.Global.Parallel.InterferenceBoundFp
import Prosa.Classic.Analysis.Global.Basic.BertognaFpTheory

/-!
Bertogna and Cirinei's response-time analysis for global FP scheduling of (potentially) parallel jobs (Rocq module
`ResponseTimeAnalysisFP` of `classic/analysis/global/parallel/bertogna_fp_theory.v`).

Representation notes:
* The section-local `Let`s are unfolded in the statements: `x tsk_other` is
  `task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R)`, `X` is
  `total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R)`,
  `workload_bound tsk_other R_other` is `W task_cost task_period tsk_other R_other R` (the parallel `W`),
  `is_hp_task` is `higher_priority_task higher_eq_priority tsk`, `hp_tasks` is
  `ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)`, and
  `response_time_bounded_by` is `is_response_time_bound_of_task … sched`; the unused `Let`s
  (`no_deadline_is_missed_by_tsk`, `task_with_response_time`, `other_scheduled_task`) are dropped.
* `\sum_(i <- s) F i` is `Prosa.Util.Sum.sumSeq s F` and `\sum_((tsk_k, R_k) <- s) F` binds the pair by pattern
  matching; `x != y` in proposition position is `(!decide (x = y)) = true`.
* The Rocq module `Export`s the classic model modules it uses; Lean clients open those namespaces directly.
* Binder lists follow the Rocq contract.
* The step "a job scheduled while `j` is backlogged belongs to another task" (inlined in the source proof of
  `bertogna_fp_all_cpus_are_busy`) reuses the accepted basic lemma
  `Prosa.Classic.Analysis.Global.Basic.BertognaFpTheory.ResponseTimeAnalysisFP.bertogna_fp_interference_by_different_tasks`,
  which does not assume sequential jobs; `bertogna_fp_too_much_interference` follows the accepted basic proof.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Parallel.BertognaFpTheory.ResponseTimeAnalysisFP

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
open Prosa.Classic.Analysis.Global.Parallel.InterferenceBoundFp.InterferenceBoundFP
open Prosa.Classic.Analysis.Global.Parallel.InterferenceBound.InterferenceBoundGeneric (interference_bound_generic)
open Prosa.Classic.Util.DivMod (div_floor ltn_div_trunc)
open Prosa.Util.Sum (sumSeq sumFiltered)
open BigOperators

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: exchanging a list sum with a double finite sum. -/
private theorem sumSeq_exchange {K : Type u} {m : Nat} (H : List K) (T : Finset Nat) (g : K → Nat → Fin m → Nat) :
    sumSeq H (fun k => ∑ t ∈ T, ∑ cpu : Fin m, g k t cpu) = ∑ t ∈ T, ∑ cpu : Fin m, sumSeq H (fun k => g k t cpu) := by
  unfold sumSeq
  induction H with
  | nil => simp
  | cons a H ih =>
    simp only [List.map_cons, List.sum_cons, ih, ← Finset.sum_add_distrib]

/-- LEAN_HELPER: in a duplicate-free list, the indicator of one element sums to its membership. -/
private theorem sumSeq_indicator {K : Type u} [DecidableEq K] (H : List K) (hnd : H.Nodup) (a : K) :
    sumSeq H (fun k => (decide (a = k)).toNat) = if a ∈ H then 1 else 0 := by
  unfold sumSeq
  induction H with
  | nil => simp
  | cons b H ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.map_cons, List.sum_cons, ih hnd.2, List.mem_cons]
    by_cases hab : a = b
    · subst hab; simp [hnd.1]
    · simp [hab]

/-! ### Lemmas about the higher-priority tasks -/

theorem bertogna_fp_workload_bounds_interference
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
    (H_all_jobs_from_taskset : ∀ j : Job, arrives_in arr_seq j → job_task j ∈ ts)
    (num_cpus : Nat)
    (sched : schedule Job num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (R : time)
    (j : Job)
    (tsk_other : sporadic_task)
    (R_other : time)
    (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ hp_bounds) :
    task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R) ≤ W task_cost task_period tsk_other R_other R := by
  by_cases hx0 : task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R) = 0
  · rw [hx0]; exact Nat.zero_le _
  unfold task_interference at hx0
  obtain ⟨t, _, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  obtain ⟨cpu, _, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hts : task_scheduled_on job_task sched tsk_other cpu t = true := by
    by_contra h
    simp only [Bool.not_eq_true] at h
    simp [h] at hne'
  unfold task_scheduled_on at hts
  cases hs : sched cpu t with
  | none => simp [hs] at hts
  | some j0 =>
      simp only [hs, decide_eq_true_eq] at hts
      have SCHED : scheduled sched j0 t = true := by
        simp only [scheduled, scheduled_on, List.any_eq_true, List.mem_finRange, true_and,
          decide_eq_true_eq]
        exact ⟨cpu, hs⟩
      have INts : tsk_other ∈ ts := by
        rw [← hts]
        exact H_all_jobs_from_taskset j0 (H_jobs_come_from_arrival_sequence j0 t SCHED)
      calc task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j) (job_arrival j + R)
          ≤ workload job_task sched tsk_other (job_arrival j) (job_arrival j + R) :=
            task_interference_le_workload job_arrival job_cost job_task sched j tsk_other _ _
        _ ≤ W task_cost task_period tsk_other R_other R :=
            workload_bounded_by_W task_cost task_period task_deadline job_arrival job_cost
              job_task job_deadline arr_seq H_valid_job_parameters sched
              H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
              H_completed_jobs_dont_execute H_sporadic_tasks tsk_other
              (H_valid_task_parameters tsk_other INts)
              (job_arrival j) R R_other
              (fun j' ARR' JOB' _ => H_response_time_of_interfering_tasks_is_known tsk_other
                R_other H_response_time_of_tsk_other j' ARR' JOB')

/-! ### Deriving a contradiction -/

theorem bertogna_fp_too_much_interference
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
    (tsk : sporadic_task)
    (hp_bounds : List (sporadic_task × time))
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period hp_bounds R) num_cpus)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true) :
    R - task_cost tsk + 1 ≤ total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) := by
  have hRe : task_cost tsk ≤ R := by
    have := H_response_time_recurrence_holds
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

theorem bertogna_fp_all_cpus_are_busy
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
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task higher_eq_priority tsk hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (R : time)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    sumSeq (ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) = total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R) * num_cpus := by
  have hnd : (ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)).Nodup := ts.nodup.filter _
  unfold task_interference total_interference
  rw [sumSeq_exchange, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [Finset.mem_Ico] at ht
  cases BACK : backlogged job_arrival job_cost sched j t
  · simp [sumSeq]
  · have PER : ∀ cpu : Fin num_cpus,
        sumSeq (ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)) (fun k => (true && task_scheduled_on job_task sched k cpu t).toNat) = 1 := by
      intro cpu
      obtain ⟨j_other, SO⟩ := H_work_conserving j t H_j_arrives BACK cpu
      have SCHo : sched cpu t = some j_other := by simpa [scheduled_on] using SO
      have SCHED : scheduled sched j_other t = true := by
        simp only [scheduled, List.any_eq_true, List.mem_finRange, true_and]
        exact ⟨cpu, SO⟩
      have ARRo := H_jobs_come_from_arrival_sequence j_other t SCHED
      have DIFF := Prosa.Classic.Analysis.Global.Basic.BertognaFpTheory.ResponseTimeAnalysisFP.bertogna_fp_interference_by_different_tasks
        task_period task_deadline job_arrival job_cost job_task arr_seq H_sporadic_tasks ts H_constrained_deadlines
        H_all_jobs_from_taskset num_cpus sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk
        task_in_ts R H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk
        H_previous_jobs_of_tsk_completed t j_other
        (by simp only [Bool.and_eq_true, decide_eq_true_eq]; omega') ARRo BACK SCHED
      have HPo := H_respects_FP_policy j j_other t H_j_arrives BACK SCHED
      have INhp : job_task j_other ∈ (ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)) := by
        rw [List.mem_filter]
        refine ⟨H_all_jobs_from_taskset j_other ARRo, ?_⟩
        simp only [higher_priority_task, Bool.and_eq_true]
        rw [H_job_of_tsk] at HPo
        exact ⟨HPo, DIFF⟩
      have EQ : (fun k => (true && task_scheduled_on job_task sched k cpu t).toNat) =
          (fun k => (decide (job_task j_other = k)).toNat) := by
        funext k
        simp [task_scheduled_on, SCHo]
      rw [EQ, sumSeq_indicator _ hnd, if_pos INhp]
    simp only [PER, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one,
      Bool.toNat_true, Nat.one_mul]

theorem bertogna_fp_sum_exceeds_total_interference
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
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_at_least_one_cpu : 0 < num_cpus)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task higher_eq_priority tsk hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period hp_bounds R) num_cpus)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    total_interference_bound_fp task_cost task_period hp_bounds R <
      sumSeq hp_bounds (fun (tsk_k, R_k) => task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) := by
  have TOOMUCH := bertogna_fp_too_much_interference task_cost task_period task_deadline job_arrival job_cost
    job_deadline job_task arr_seq H_valid_job_parameters num_cpus sched H_jobs_must_arrive_to_execute tsk hp_bounds R
    H_response_time_recurrence_holds j H_j_arrives H_job_of_tsk H_j_not_completed
  have ALLBUSY := bertogna_fp_all_cpus_are_busy task_cost task_period task_deadline job_arrival job_cost job_task
    arr_seq H_sporadic_tasks ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority
    H_work_conserving H_respects_FP_policy tsk task_in_ts hp_bounds H_hp_bounds_has_interfering_tasks R
    H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk H_previous_jobs_of_tsk_completed
  have hHnd : (ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)).Nodup := ts.nodup.filter _
  have hsub : sumSeq (ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)) (fun tsk_k => task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) ≤
      sumSeq hp_bounds (fun (tsk_k, R_k) => task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) := by
    have := Prosa.Classic.Util.Sum.leq_sum_sub_uniq _ (ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)) (hp_bounds.map Prod.fst)
      (fun tsk_k => task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R)) hHnd (by
        intro k hk
        rw [List.mem_filter] at hk
        obtain ⟨R0, hR0⟩ := H_hp_bounds_has_interfering_tasks k hk.1 (by simpa using hk.2)
        exact List.mem_map.mpr ⟨(k, R0), hR0, rfl⟩)
    refine le_trans this (le_of_eq ?_)
    unfold sumSeq
    rw [List.map_map]
    rfl
  have REC := H_response_time_recurrence_holds
  unfold div_floor at REC
  apply ltn_div_trunc _ _ num_cpus H_at_least_one_cpu
  have hdiv : total_interference_bound_fp task_cost task_period hp_bounds R / num_cpus =
      R - task_cost tsk := by omega'
  rw [hdiv]
  apply Nat.lt_of_lt_of_le (Nat.lt_succ_self _)
  rw [Nat.le_div_iff_mul_le H_at_least_one_cpu]
  refine le_trans ?_ hsub
  rw [ALLBUSY]
  exact Nat.mul_le_mul_right _ TOOMUCH

theorem bertogna_fp_exists_task_that_exceeds_bound
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
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_at_least_one_cpu : 0 < num_cpus)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task higher_eq_priority tsk hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period hp_bounds R) num_cpus)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk)
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_j_not_completed : (!completed job_cost sched j (job_arrival j + R)) = true)
    (H_previous_jobs_of_tsk_completed :
      ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true) :
    ∃ (tsk_k : sporadic_task) (R_k : time),
      (tsk_k, R_k) ∈ hp_bounds ∧ W task_cost task_period tsk_k R_k R < task_interference job_arrival job_cost job_task sched j tsk_k (job_arrival j) (job_arrival j + R) := by
  have SUM := bertogna_fp_sum_exceeds_total_interference task_cost task_period task_deadline job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute higher_eq_priority H_work_conserving H_respects_FP_policy H_at_least_one_cpu tsk task_in_ts hp_bounds H_hp_bounds_has_interfering_tasks R H_response_time_recurrence_holds H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk H_j_not_completed H_previous_jobs_of_tsk_completed
  by_contra NOT
  simp only [not_exists, not_and, Nat.not_lt] at NOT
  apply absurd SUM
  apply Nat.not_lt.mpr
  unfold total_interference_bound_fp sumSeq
  apply List.sum_le_sum
  rintro ⟨k, Rk⟩ hk
  simp only [interference_bound_generic]
  exact NOT k Rk hk

/-! ### Main theorem -/

theorem bertogna_cirinei_response_time_bound_fp
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
    (higher_eq_priority : FP_policy sporadic_task)
    (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)
    (H_at_least_one_cpu : 0 < num_cpus)
    (tsk : sporadic_task)
    (task_in_ts : tsk ∈ ts)
    (hp_bounds : List (sporadic_task × time))
    (H_response_time_of_interfering_tasks_is_known :
      ∀ (hp_tsk : sporadic_task) (R : time), (hp_tsk, R) ∈ hp_bounds →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)
    (H_hp_bounds_has_interfering_tasks :
      ∀ hp_tsk : sporadic_task, hp_tsk ∈ ts →
        higher_priority_task higher_eq_priority tsk hp_tsk = true →
        ∃ R : time, (hp_tsk, R) ∈ hp_bounds)
    (R : time)
    (H_response_time_recurrence_holds :
      R = task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period hp_bounds R) num_cpus)
    (H_response_time_no_larger_than_deadline : R ≤ task_deadline tsk) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  suffices MAIN : ∀ (n : Nat) (j : Job), job_arrival j = n → arrives_in arr_seq j →
      job_task j = tsk → completed job_cost sched j (job_arrival j + R) = true by
    intro j ARRj JOBtsk
    exact MAIN _ j rfl ARRj JOBtsk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j hn ARRj JOBtsk
    by_contra NOTCOMP
    have NOTCOMP' : (!completed job_cost sched j (job_arrival j + R)) = true := by
      simpa using NOTCOMP
    have BEFOREok : ∀ j0 : Job, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j →
        completed job_cost sched j0 (job_arrival j0 + R) = true :=
      fun j0 ARR0 JOB0 LT0 => IH (job_arrival j0) (hn ▸ LT0) j0 rfl ARR0 JOB0
    obtain ⟨tsk_k, R_k, HPk, LT⟩ := bertogna_fp_exists_task_that_exceeds_bound task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts
      H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      higher_eq_priority H_work_conserving H_respects_FP_policy H_at_least_one_cpu tsk task_in_ts hp_bounds
      H_hp_bounds_has_interfering_tasks R H_response_time_recurrence_holds H_response_time_no_larger_than_deadline j
      ARRj JOBtsk NOTCOMP' BEFOREok
    have WORKLOAD := bertogna_fp_workload_bounds_interference task_cost task_period task_deadline job_arrival
      job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute hp_bounds H_response_time_of_interfering_tasks_is_known R j tsk_k R_k HPk
    exact absurd LT (Nat.not_lt.mpr WORKLOAD)

end Prosa.Classic.Analysis.Global.Parallel.BertognaFpTheory.ResponseTimeAnalysisFP
