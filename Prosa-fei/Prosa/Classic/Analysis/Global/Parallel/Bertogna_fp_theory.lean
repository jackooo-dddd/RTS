-- Translated from: ../rt-proofs/classic/analysis/global/parallel/bertogna_fp_theory.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Global.Workload
import Prosa.Classic.Model.Schedule.Global.Basic.Schedule
import Prosa.Classic.Analysis.Global.Parallel.Workload_bound
import Prosa.Classic.Model.Schedule.Global.Schedulability
import Prosa.Classic.Model.Schedule.Global.Response_time
import Prosa.Classic.Model.Schedule.Global.Basic.Platform
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

set_option autoImplicit false

namespace Prosa.Classic.Analysis.Global.Parallel.Bertogna_fp_theory

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.Basic.Platform.Platform
open Prosa.Classic.Model.Schedule.Global.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound
open Prosa.Util.Div_mod

attribute [local instance] Classical.propDecidable

namespace ResponseTimeAnalysisFP

noncomputable def total_interference
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (j : Job) (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    if backlogged job_arrival job_cost sched j t then 1 else 0

noncomputable def task_interference
    {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_task : Job → sporadic_task)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (j : Job) (tsk_other : sporadic_task) (t1 t2 : Time) : ℕ :=
  ∑ t ∈ Finset.Ico t1 t2,
    ∑ cpu : Fin num_cpus,
      if (backlogged job_arrival job_cost sched j t ∧
          task_scheduled_on job_task sched tsk_other cpu t = true) then 1 else 0

def interference_bound_generic
    {sporadic_task : Type _} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → Time) (task_period : sporadic_task → Time)
    (delta : Time) (tsk_R : sporadic_task × Time) : ℕ :=
  W task_cost task_period tsk_R.1 tsk_R.2 delta

def total_interference_bound_fp
    {sporadic_task : Type _} [DecidableEq sporadic_task]
    (task_cost : sporadic_task → Time) (task_period : sporadic_task → Time)
    (hp_bounds : List (sporadic_task × Time)) (delta : Time) : ℕ :=
  (hp_bounds.map (fun tsk_R => interference_bound_generic task_cost task_period delta tsk_R)).sum

theorem task_interference_le_workload
    {sporadic_task : Type _} [DecidableEq sporadic_task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time) (job_cost : Job → Time)
    (job_task : Job → sporadic_task)
    {num_cpus : ℕ} (sched : schedule Job num_cpus)
    (j : Job) (tsk_other : sporadic_task) (t1 t2 : Time) :
    task_interference job_arrival job_cost job_task sched j tsk_other t1 t2 ≤
      Prosa.Classic.Model.Schedule.Global.Workload.workload job_task sched tsk_other t1 t2 := by
  unfold task_interference Prosa.Classic.Model.Schedule.Global.Workload.workload
  apply Finset.sum_le_sum
  intro t _
  apply Finset.sum_le_sum
  intro cpu _
  unfold task_scheduled_on Prosa.Classic.Model.Schedule.Global.Workload.service_of_task
  cases h_sched : sched cpu t with
  | none => by_cases h_back : backlogged job_arrival job_cost sched j t <;> simp [h_back]
  | some j' =>
    simp only []
    by_cases h_back : backlogged job_arrival job_cost sched j t
    · simp only [h_back, true_and]
      by_cases h_task : job_task j' = tsk_other
      · simp [h_task]
      · simp [h_task]
    · simp only [h_back, false_and, ite_false]
      exact Nat.zero_le _

section ResponseTimeBound

variable {sporadic_task : Type _} [DecidableEq sporadic_task]
variable (task_cost : sporadic_task → Time)
variable (task_period : sporadic_task → Time)
variable (task_deadline : sporadic_task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_cost : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → sporadic_task)

variable (arr_seq : arrival_sequence Job)

variable (H_sporadic_tasks :
  sporadic_task_model task_period job_arrival job_task arr_seq)
variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable (ts : List sporadic_task)
variable (H_valid_task_parameters :
  valid_sporadic_taskset task_cost task_period task_deadline ts)
variable (H_constrained_deadlines :
  ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)

variable (H_ts_uniq : ts.Nodup)

variable (H_all_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable {num_cpus : ℕ}
variable (sched : schedule Job num_cpus)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)
variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (higher_eq_priority : FP_policy sporadic_task)

variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
variable (H_respects_FP_policy :
  respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)

variable (H_at_least_one_cpu : num_cpus > 0)

variable (tsk : sporadic_task)
variable (task_in_ts : tsk ∈ ts)

variable (hp_bounds : List (sporadic_task × Time))
variable (H_response_time_of_interfering_tasks_is_known :
  ∀ hp_tsk R,
    (hp_tsk, R) ∈ hp_bounds →
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched hp_tsk R)

variable (H_hp_bounds_has_interfering_tasks :
  ∀ hp_tsk,
    hp_tsk ∈ ts →
    higher_priority_task higher_eq_priority tsk hp_tsk = true →
    ∃ R, (hp_tsk, R) ∈ hp_bounds)

variable (R : Time)
variable (H_response_time_recurrence_holds :
  R = task_cost tsk +
      div_floor
        (total_interference_bound_fp task_cost task_period hp_bounds R)
        num_cpus)

variable (H_response_time_no_larger_than_deadline :
  R ≤ task_deadline tsk)

section Lemmas

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (H_j_not_completed : ¬ completed job_cost sched j (job_arrival j + R))
variable (H_previous_jobs_of_tsk_completed :
  ∀ j0,
    arrives_in arr_seq j0 →
    job_task j0 = tsk →
    job_arrival j0 < job_arrival j →
    completed job_cost sched j0 (job_arrival j0 + R))

section LemmasAboutHPTasks

variable (tsk_other : sporadic_task)
variable (R_other : Time)
variable (H_response_time_of_tsk_other : (tsk_other, R_other) ∈ hp_bounds)

include H_valid_job_parameters H_valid_task_parameters H_constrained_deadlines
  H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sporadic_tasks H_response_time_of_interfering_tasks_is_known
  H_response_time_of_tsk_other
  H_j_arrives H_job_of_tsk in
theorem bertogna_fp_workload_bounds_interference :
    task_interference job_arrival job_cost job_task sched j
      tsk_other (job_arrival j) (job_arrival j + R) ≤
      W task_cost task_period tsk_other R_other R := by
  -- Case split: does tsk_other get scheduled anywhere in [arr j, arr j + R)?
  by_cases h_sched :
    ∃ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      ∃ cpu : Fin num_cpus, task_scheduled_on job_task sched tsk_other cpu t = true
  · -- Some j0 is scheduled as tsk_other at some t; derive tsk_other ∈ ts.
    obtain ⟨t, _, cpu, h_ts⟩ := h_sched
    unfold task_scheduled_on at h_ts
    split at h_ts
    · next j0 h_eq =>
      have h_task_j0 : job_task j0 = tsk_other := by
        simpa [decide_eq_true_eq] using h_ts
      have h_scheduled : scheduled sched j0 t := ⟨cpu, by
        unfold scheduled_on; simp [h_eq]⟩
      have h_arr0 : arrives_in arr_seq j0 :=
        H_jobs_come_from_arrival_sequence j0 t h_scheduled
      have h_tsk_in_ts : tsk_other ∈ ts := by
        have := H_all_jobs_from_taskset j0 h_arr0
        simpa [h_task_j0] using this
      -- Reduce to workload via task_interference_le_workload + workload_bounded_by_W.
      have h_ti_le_wl :=
        task_interference_le_workload job_arrival job_cost job_task sched
          j tsk_other (job_arrival j) (job_arrival j + R)
      have h_valid_other : is_valid_sporadic_task task_cost task_period task_deadline tsk_other :=
        H_valid_task_parameters tsk_other h_tsk_in_ts
      have h_rtb_other : ∀ (j0 : Job),
          Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j0 →
          job_task j0 = tsk_other →
          job_arrival j0 + R_other < job_arrival j + R →
          completed job_cost sched j0 (job_arrival j0 + R_other) := by
        intro j0 h_arr0 h_tsk0 _
        exact H_response_time_of_interfering_tasks_is_known tsk_other R_other
          H_response_time_of_tsk_other j0 h_arr0 h_tsk0
      have h_wl_le_W :
          Prosa.Classic.Model.Schedule.Global.Workload.workload
            job_task sched tsk_other (job_arrival j) (job_arrival j + R) ≤
          Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound.W
            task_cost task_period tsk_other R_other R := by
        have h :
            Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound.workload
              job_task sched tsk_other (job_arrival j) (job_arrival j + R) ≤
            Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound.W
              task_cost task_period tsk_other R_other R := by
          apply Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound.workload_bounded_by_W
            task_cost task_period task_deadline job_arrival job_cost job_task job_deadline arr_seq
            H_valid_job_parameters sched
            H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
            H_completed_jobs_dont_execute H_sporadic_tasks tsk_other h_valid_other
          exact h_rtb_other
        -- Bridge between the two `workload` defs (defeq up to ite vs decide).
        have h_eq :
            Prosa.Classic.Model.Schedule.Global.Workload.workload
              job_task sched tsk_other (job_arrival j) (job_arrival j + R) =
            Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound.workload
              job_task sched tsk_other (job_arrival j) (job_arrival j + R) := by
          unfold Prosa.Classic.Model.Schedule.Global.Workload.workload
                 Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound.workload
          refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun cpu _ => ?_))
          unfold Prosa.Classic.Model.Schedule.Global.Workload.service_of_task
                 Prosa.Classic.Analysis.Global.Parallel.Workload_bound.WorkloadBound.service_of_task
          cases sched cpu t with
          | none => rfl
          | some j' => by_cases h : job_task j' = tsk_other <;> simp [h]
        rw [h_eq]; exact h
      exact le_trans h_ti_le_wl h_wl_le_W
    · exact absurd h_ts (by simp)
  · -- tsk_other never scheduled ⇒ task_interference = 0.
    push_neg at h_sched
    have h_zero :
        task_interference job_arrival job_cost job_task sched j
          tsk_other (job_arrival j) (job_arrival j + R) = 0 := by
      unfold task_interference
      apply Finset.sum_eq_zero
      intro t ht
      apply Finset.sum_eq_zero
      intro cpu _
      have h_not : task_scheduled_on job_task sched tsk_other cpu t ≠ true :=
        fun h => h_sched t ht cpu h
      simp [h_not]
    rw [h_zero]; exact Nat.zero_le _

end LemmasAboutHPTasks

section DerivingContradiction

noncomputable def other_scheduled_task (t : Time) (tsk_other : sporadic_task) : Prop :=
  task_is_scheduled job_task sched tsk_other t ∧
  higher_priority_task higher_eq_priority tsk tsk_other = true

include H_completed_jobs_dont_execute H_valid_job_parameters
  H_response_time_recurrence_holds H_j_arrives H_job_of_tsk
  H_j_not_completed H_jobs_must_arrive_to_execute in
theorem bertogna_fp_too_much_interference :
    total_interference job_arrival job_cost sched j
      (job_arrival j) (job_arrival j + R) ≥ R - task_cost tsk + 1 := by
  -- job_cost j ≤ task_cost tsk (from valid_sporadic_job)
  have h_cost_le : job_cost j ≤ task_cost tsk := by
    have hv := H_valid_job_parameters j H_j_arrives
    have h := hv.2.1
    unfold job_cost_le_task_cost at h
    rw [H_job_of_tsk] at h; exact h
  -- service(arr+R) < job_cost j (not completed)
  have h_service_lt : service sched j (job_arrival j + R) < job_cost j := by
    unfold completed at H_j_not_completed
    omega
  -- service_during [arr, arr+R) = service (arr+R)
  have h_service_split : service sched j (job_arrival j + R)
      = service_during sched j (job_arrival j) (job_arrival j + R) := by
    unfold service service_during
    rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le _) (Nat.le_add_right _ R)]
    rw [cumulative_service_before_job_arrival_zero
          job_arrival sched j H_jobs_must_arrive_to_execute 0 (job_arrival j) (le_refl _)]
    simp
  have h_sd_lt : service_during sched j (job_arrival j) (job_arrival j + R) < job_cost j := by
    rw [← h_service_split]; exact h_service_lt
  -- Each t in [arr, arr+R): backlogged + service_at ≥ 1
  have h_each : ∀ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      1 ≤ (if backlogged job_arrival job_cost sched j t then 1 else 0) + service_at sched j t := by
    intro t ht
    rw [Finset.mem_Ico] at ht
    by_cases h_bl : backlogged job_arrival job_cost sched j t
    · simp [h_bl]
    · -- j is pending at t (arrived, not completed), so either backlogged or scheduled.
      have h_pending : pending job_arrival job_cost sched j t := by
        refine ⟨ht.1, ?_⟩
        intro h_comp
        exact H_j_not_completed
          (completion_monotonic job_cost sched j H_completed_jobs_dont_execute
             t (job_arrival j + R) (Nat.le_of_lt ht.2) h_comp)
      have h_sched : scheduled sched j t := by
        by_contra h_not_sched
        exact h_bl ⟨h_pending, h_not_sched⟩
      have h_serv_pos : 1 ≤ service_at sched j t := by
        rw [Nat.one_le_iff_ne_zero]
        intro h_zero
        exact (not_scheduled_no_service sched j t).mpr h_zero h_sched
      by_cases h_bl' : backlogged job_arrival job_cost sched j t
      · simp [h_bl']
      · simp [h_bl']; exact h_serv_pos
  -- Sum: total_interference + service_during ≥ R
  have h_sum :
      total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R)
      + service_during sched j (job_arrival j) (job_arrival j + R) ≥ R := by
    unfold total_interference service_during
    rw [← Finset.sum_add_distrib]
    have h_card : (Finset.Ico (job_arrival j) (job_arrival j + R)).card = R := by
      rw [Nat.card_Ico]; omega
    calc R = ∑ _t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), 1 := by
              rw [Finset.sum_const, smul_eq_mul, mul_one, h_card]
         _ ≤ ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
             ((if backlogged job_arrival job_cost sched j t then 1 else 0)
              + service_at sched j t) := Finset.sum_le_sum h_each
  have h_R_ge : R ≥ task_cost tsk := by
    rw [H_response_time_recurrence_holds]; exact Nat.le_add_right _ _
  have h_sd_lt_cost :
      service_during sched j (job_arrival j) (job_arrival j + R) < task_cost tsk :=
    Nat.lt_of_lt_of_le h_sd_lt h_cost_le
  -- Purely-arithmetic closure: ∀ T S d, T + S ≥ R → S < d → R ≥ d → T ≥ R - d + 1.
  suffices h : ∀ (r T S d : ℕ), T + S ≥ r → S < d → r ≥ d → T ≥ r - d + 1 by
    exact h _ _ _ _ h_sum h_sd_lt_cost h_R_ge
  intros; omega

include H_all_jobs_from_taskset H_valid_task_parameters
  H_constrained_deadlines H_ts_uniq H_jobs_come_from_arrival_sequence
  H_sporadic_tasks H_work_conserving H_respects_FP_policy
  H_response_time_no_larger_than_deadline
  H_previous_jobs_of_tsk_completed H_completed_jobs_dont_execute
  H_jobs_must_arrive_to_execute H_valid_job_parameters
  H_j_arrives H_job_of_tsk in
set_option maxHeartbeats 1600000 in
theorem bertogna_fp_all_cpus_are_busy :
    ((ts.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)).map
      (fun tsk_k => task_interference job_arrival job_cost job_task sched j
        tsk_k (job_arrival j) (job_arrival j + R))).sum =
      total_interference job_arrival job_cost sched j
        (job_arrival j) (job_arrival j + R) * num_cpus := by
  set hp_tasks := ts.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)
  have h_tsk_in := (H_job_of_tsk ▸ H_all_jobs_from_taskset j H_j_arrives : tsk ∈ ts)
  -- Exchange list sum past finset sums
  have h_exch : ∀ (l : List sporadic_task),
      (l.map (fun tsk_k =>
        task_interference job_arrival job_cost job_task sched j
          tsk_k (job_arrival j) (job_arrival j + R))).sum =
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), ∑ cpu : Fin num_cpus,
        (l.map (fun tsk_k =>
          if (backlogged job_arrival job_cost sched j t ∧
              task_scheduled_on job_task sched tsk_k cpu t = true) then 1 else 0)).sum := by
    intro l; induction l with
    | nil => simp [task_interference]
    | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih]
      unfold task_interference
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro cpu _
      simp [List.map_cons, List.sum_cons]
  rw [h_exch]
  -- RHS: TI * num_cpus = ∑ t, (if bl then 1 else 0) * num_cpus
  unfold total_interference
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro t ht
  -- Split on backlogged
  by_cases hbl : backlogged job_arrival job_cost sched j t
  · simp only [hbl, true_and, ite_true]
    -- Goal: ∑ cpu, (hp_tasks.map ...).sum = 1 * num_cpus
    rw [one_mul]
    suffices h_one : ∀ cpu : Fin num_cpus,
        (hp_tasks.map (fun tsk_k =>
          if task_scheduled_on job_task sched tsk_k cpu t = true then (1 : ℕ) else 0)).sum = 1 by
      calc ∑ cpu : Fin num_cpus, _ = ∑ _cpu : Fin num_cpus, (1 : ℕ) :=
            Finset.sum_congr rfl (fun cpu _ => h_one cpu)
        _ = num_cpus := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                              smul_eq_mul, mul_one]
    intro cpu
    -- Per-cpu: show the indicator sum over hp_tasks = 1
    obtain ⟨j_other, h_on⟩ := H_work_conserving j t H_j_arrives hbl cpu
    have h_sched_eq : sched cpu t = some j_other := eq_of_beq h_on
    have h_sched_j : scheduled sched j_other t := ⟨cpu, h_on⟩
    have h_arr_jo := H_jobs_come_from_arrival_sequence j_other t h_sched_j
    have h_in_ts := H_all_jobs_from_taskset j_other h_arr_jo
    have h_hp : higher_eq_priority (job_task j_other) (job_task j) = true :=
      H_respects_FP_policy j j_other t H_j_arrives hbl h_sched_j
    rw [H_job_of_tsk] at h_hp
    -- j_other's task ≠ tsk (sporadic model)
    have h_neq : job_task j_other ≠ tsk := by
      intro h_same
      have h_ne : j_other ≠ j := fun h => hbl.2 (h ▸ h_sched_j)
      have h_arr_le : job_arrival j_other ≤ t := H_jobs_must_arrive_to_execute j_other t h_sched_j
      have h_j_arr : job_arrival j ≤ t := hbl.1.1
      have h_R_le : R ≤ task_period tsk :=
        Nat.le_trans H_response_time_no_larger_than_deadline (H_constrained_deadlines tsk h_tsk_in)
      rcases Nat.lt_or_ge (job_arrival j_other) (job_arrival j) with h_lt | h_le
      · have h_comp := H_previous_jobs_of_tsk_completed j_other h_arr_jo h_same h_lt
        have h_spor := H_sporadic_tasks j_other j h_ne h_arr_jo H_j_arrives
            (h_same.trans H_job_of_tsk.symm) (Nat.le_of_lt h_lt)
        rw [h_same] at h_spor
        have h_le_t : job_arrival j_other + R ≤ t :=
          le_trans (le_trans (Nat.add_le_add_left h_R_le _) h_spor) h_j_arr
        have h_comp_t := completion_monotonic job_cost sched j_other H_completed_jobs_dont_execute
            (job_arrival j_other + R) t h_le_t h_comp
        exact absurd h_sched_j (completed_implies_not_scheduled job_cost sched j_other
            H_completed_jobs_dont_execute t h_comp_t)
      · have h_spor := H_sporadic_tasks j j_other h_ne.symm H_j_arrives h_arr_jo
            (H_job_of_tsk.trans h_same.symm) h_le
        rw [H_job_of_tsk] at h_spor
        have h_ub := (Finset.mem_Ico.mp ht).2
        exact absurd (lt_of_lt_of_le h_ub (Nat.add_le_add_left h_R_le _))
          (not_lt.mpr (le_trans h_spor h_arr_le))
    -- job_task j_other is in hp_tasks
    have h_hp_task : higher_priority_task higher_eq_priority tsk (job_task j_other) = true := by
      unfold higher_priority_task; simp [h_hp, h_neq]
    have h_in_hp : job_task j_other ∈ hp_tasks := by
      simp only [hp_tasks, List.mem_filter]; exact ⟨h_in_ts, h_hp_task⟩
    -- hp_tasks has no duplicates
    have h_nodup : hp_tasks.Nodup := H_ts_uniq.filter _
    -- The indicator depends only on whether tsk_k = job_task j_other
    have h_indicator : ∀ tsk_k, tsk_k ∈ hp_tasks →
        (if task_scheduled_on job_task sched tsk_k cpu t = true then (1 : ℕ) else 0) =
        (if tsk_k = job_task j_other then 1 else 0) := by
      intro tsk_k _
      unfold task_scheduled_on; rw [h_sched_eq]
      simp [decide_eq_true_eq, eq_comm]
    rw [List.map_congr_left h_indicator]
    -- Sum of (if tsk_k = a then 1 else 0) over nodup list containing a = 1
    clear h_indicator h_sched_eq h_sched_j h_arr_jo h_in_ts h_hp h_neq h_hp_task
    clear_value hp_tasks
    induction hp_tasks with
    | nil => simp at h_in_hp
    | cons b l ih =>
      simp only [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp h_in_hp with h_eq | h_mem
      · subst h_eq; simp only [ite_true]
        suffices (l.map (fun x => if x = job_task j_other then (1 : ℕ) else 0)).sum = 0 by omega
        apply List.sum_eq_zero
        intro x hx; rw [List.mem_map] at hx
        obtain ⟨a, ha, rfl⟩ := hx
        have : a ≠ job_task j_other :=
          fun h => by subst h; exact (List.nodup_cons.mp h_nodup).1 ha
        simp [this]
      · have h_ne_b : b ≠ job_task j_other :=
          fun h => by subst h; exact (List.nodup_cons.mp h_nodup).1 h_mem
        rw [if_neg h_ne_b]; simp only [Nat.zero_add]
        exact ih h_mem (List.nodup_cons.mp h_nodup).2
  · simp only [hbl, false_and, ite_false]
    simp

include H_completed_jobs_dont_execute H_valid_job_parameters
  H_response_time_recurrence_holds H_j_arrives H_job_of_tsk
  H_j_not_completed H_all_jobs_from_taskset H_valid_task_parameters
  H_constrained_deadlines H_jobs_come_from_arrival_sequence
  H_sporadic_tasks H_work_conserving H_respects_FP_policy
  H_response_time_no_larger_than_deadline
  H_previous_jobs_of_tsk_completed
  H_hp_bounds_has_interfering_tasks H_at_least_one_cpu
  H_jobs_must_arrive_to_execute in
set_option maxHeartbeats 800000 in
theorem bertogna_fp_sum_exceeds_total_interference :
    (hp_bounds.map (fun p =>
      task_interference job_arrival job_cost job_task sched j
        p.1 (job_arrival j) (job_arrival j + R))).sum >
      total_interference_bound_fp task_cost task_period hp_bounds R := by
  -- Step 1: TI ≥ R - task_cost tsk + 1
  have hTOO := bertogna_fp_too_much_interference task_cost task_period task_deadline
    job_arrival job_cost job_deadline job_task arr_seq H_valid_job_parameters sched
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk hp_bounds R
    H_response_time_recurrence_holds j H_j_arrives H_job_of_tsk H_j_not_completed
  set TI := total_interference job_arrival job_cost sched j (job_arrival j) (job_arrival j + R)
  set bound := total_interference_bound_fp task_cost task_period hp_bounds R
  -- Step 2: TI * num_cpus > bound (arithmetic)
  have hR_eq : R = task_cost tsk + bound / num_cpus := by
    rw [H_response_time_recurrence_holds]; unfold div_floor; rfl
  have hTI_ge : TI ≥ bound / num_cpus + 1 := by
    have h_sub : R - task_cost tsk = bound / num_cpus := by
      rw [hR_eq, Nat.add_comm (task_cost tsk) (bound / num_cpus)]
      exact @Nat.add_sub_cancel (bound / num_cpus) (task_cost tsk)
    calc bound / num_cpus + 1 = R - task_cost tsk + 1 := by rw [h_sub]
      _ ≤ TI := hTOO
  have hArith : TI * num_cpus > bound := by
    calc bound < (bound / num_cpus + 1) * num_cpus := by
            have := Nat.div_add_mod bound num_cpus
            have := Nat.mod_lt bound H_at_least_one_cpu; nlinarith
      _ ≤ TI * num_cpus := Nat.mul_le_mul_right _ hTI_ge
  -- Step 3: Covering — sum ≥ TI * num_cpus
  suffices hCov : (hp_bounds.map (fun p =>
    task_interference job_arrival job_cost job_task sched j
      p.1 (job_arrival j) (job_arrival j + R))).sum ≥ TI * num_cpus by omega
  -- Key covering lemma: at each backlogged t and each cpu, some hp_bounds entry matches
  have hp_cover : ∀ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
      backlogged job_arrival job_cost sched j t →
      ∀ cpu : Fin num_cpus,
      ∃ (tsk_hp : sporadic_task) (R_hp : Time),
        (tsk_hp, R_hp) ∈ hp_bounds ∧
        task_scheduled_on job_task sched tsk_hp cpu t = true := by
    intro t ht hbl cpu
    obtain ⟨j_other, h_on⟩ := H_work_conserving j t H_j_arrives hbl cpu
    have h_sched_eq : sched cpu t = some j_other := eq_of_beq h_on
    have h_sched_j : scheduled sched j_other t := ⟨cpu, h_on⟩
    have h_arr_jo := H_jobs_come_from_arrival_sequence j_other t h_sched_j
    have h_in_ts := H_all_jobs_from_taskset j_other h_arr_jo
    have h_hp : higher_eq_priority (job_task j_other) (job_task j) = true :=
      H_respects_FP_policy j j_other t H_j_arrives hbl h_sched_j
    rw [H_job_of_tsk] at h_hp
    have h_tsk_in := (H_job_of_tsk ▸ H_all_jobs_from_taskset j H_j_arrives : tsk ∈ ts)
    -- j_other's task ≠ tsk (sporadic model)
    have h_neq : job_task j_other ≠ tsk := by
      intro h_same
      have h_ne : j_other ≠ j := fun h => hbl.2 (h ▸ h_sched_j)
      have h_arr_le : job_arrival j_other ≤ t := H_jobs_must_arrive_to_execute j_other t h_sched_j
      have h_j_arr : job_arrival j ≤ t := hbl.1.1
      have h_R_le : R ≤ task_period tsk :=
        Nat.le_trans H_response_time_no_larger_than_deadline (H_constrained_deadlines tsk h_tsk_in)
      rcases Nat.lt_or_ge (job_arrival j_other) (job_arrival j) with h_lt | h_le
      · have h_comp := H_previous_jobs_of_tsk_completed j_other h_arr_jo h_same h_lt
        have h_spor := H_sporadic_tasks j_other j h_ne h_arr_jo H_j_arrives
            (h_same.trans H_job_of_tsk.symm) (Nat.le_of_lt h_lt)
        rw [h_same] at h_spor
        have h_le_t : job_arrival j_other + R ≤ t :=
          le_trans (le_trans (Nat.add_le_add_left h_R_le _) h_spor) h_j_arr
        have h_comp_t := completion_monotonic job_cost sched j_other H_completed_jobs_dont_execute
            (job_arrival j_other + R) t h_le_t h_comp
        exact absurd h_sched_j (completed_implies_not_scheduled job_cost sched j_other
            H_completed_jobs_dont_execute t h_comp_t)
      · have h_spor := H_sporadic_tasks j j_other h_ne.symm H_j_arrives h_arr_jo
            (H_job_of_tsk.trans h_same.symm) h_le
        rw [H_job_of_tsk] at h_spor
        have h_ub := (Finset.mem_Ico.mp ht).2
        exact absurd (lt_of_lt_of_le h_ub (Nat.add_le_add_left h_R_le _))
          (not_lt.mpr (le_trans h_spor h_arr_le))
    have h_hp_task : higher_priority_task higher_eq_priority tsk (job_task j_other) = true := by
      unfold higher_priority_task; simp [h_hp, h_neq]
    obtain ⟨R_k, h_entry⟩ := H_hp_bounds_has_interfering_tasks (job_task j_other) h_in_ts h_hp_task
    exact ⟨job_task j_other, R_k, h_entry, by unfold task_scheduled_on; rw [h_sched_eq]; simp⟩
  -- Exchange list sum past both finset sums in one step
  have h_exch : ∀ (l : List (sporadic_task × Time)),
      (l.map (fun p =>
        task_interference job_arrival job_cost job_task sched j
          p.1 (job_arrival j) (job_arrival j + R))).sum =
      ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R), ∑ cpu : Fin num_cpus,
        (l.map (fun p =>
          if (backlogged job_arrival job_cost sched j t ∧
              task_scheduled_on job_task sched p.1 cpu t = true) then 1 else 0)).sum := by
    intro l; induction l with
    | nil => simp [task_interference]
    | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih]
      unfold task_interference
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro t _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro cpu _
      simp [List.map_cons, List.sum_cons]
  rw [h_exch]
  -- Now goal: ∑ t ∑ cpu, (hp_bounds.map ...).sum ≥ TI * num_cpus
  -- Expand TI * m = ∑ t (if bl then 1 else 0) * m = ∑ t ∑ cpu (if bl then 1 else 0)
  change _ ≥ (∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + R),
    if backlogged job_arrival job_cost sched j t then 1 else 0) * num_cpus
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum; intro t ht
  rw [show (if backlogged job_arrival job_cost sched j t then (1:ℕ) else 0) * num_cpus =
    ∑ _cpu : Fin num_cpus, (if backlogged job_arrival job_cost sched j t then (1:ℕ) else 0) from by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm]]
  apply Finset.sum_le_sum; intro cpu _
  by_cases hbl : backlogged job_arrival job_cost sched j t
  · simp only [hbl, true_and, ite_true]
    obtain ⟨tsk_hp, R_hp, h_entry, h_ts_on⟩ := hp_cover t ht hbl cpu
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _
      (List.mem_map.mpr ⟨(tsk_hp, R_hp), h_entry, by simp [h_ts_on]⟩)
  · simp only [hbl, false_and, ite_false]; exact Nat.zero_le _

include H_completed_jobs_dont_execute H_valid_job_parameters
  H_response_time_recurrence_holds H_j_arrives H_job_of_tsk
  H_j_not_completed H_all_jobs_from_taskset H_valid_task_parameters
  H_constrained_deadlines H_jobs_come_from_arrival_sequence
  H_sporadic_tasks H_work_conserving H_respects_FP_policy
  H_response_time_no_larger_than_deadline
  H_previous_jobs_of_tsk_completed
  H_hp_bounds_has_interfering_tasks H_at_least_one_cpu
  H_jobs_must_arrive_to_execute in
theorem bertogna_fp_exists_task_that_exceeds_bound :
    ∃ tsk_k R_k,
      (tsk_k, R_k) ∈ hp_bounds ∧
      task_interference job_arrival job_cost job_task sched j
        tsk_k (job_arrival j) (job_arrival j + R) >
        W task_cost task_period tsk_k R_k R := by
  have h_sum : (hp_bounds.map (fun p =>
      task_interference job_arrival job_cost job_task sched j
        p.1 (job_arrival j) (job_arrival j + R))).sum >
      total_interference_bound_fp task_cost task_period hp_bounds R :=
    bertogna_fp_sum_exceeds_total_interference task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts
      H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      higher_eq_priority H_work_conserving H_respects_FP_policy H_at_least_one_cpu tsk
      hp_bounds H_hp_bounds_has_interfering_tasks R H_response_time_recurrence_holds
      H_response_time_no_larger_than_deadline j H_j_arrives H_job_of_tsk H_j_not_completed
      H_previous_jobs_of_tsk_completed
  by_contra h_not
  push_neg at h_not
  have h_le : (hp_bounds.map (fun p =>
      task_interference job_arrival job_cost job_task sched j
        p.1 (job_arrival j) (job_arrival j + R))).sum ≤
      total_interference_bound_fp task_cost task_period hp_bounds R := by
    unfold total_interference_bound_fp interference_bound_generic
    -- Need to show sum of task_interference ≤ sum of W
    -- When h_not says each task_interference ≤ W
    -- Use induction on the list
    suffices h : ∀ (l : List (sporadic_task × Time)),
        (∀ tsk_k R_k, (tsk_k, R_k) ∈ l →
          task_interference job_arrival job_cost job_task sched j
            tsk_k (job_arrival j) (job_arrival j + R) ≤
            W task_cost task_period tsk_k R_k R) →
        (l.map (fun p =>
          task_interference job_arrival job_cost job_task sched j
            p.1 (job_arrival j) (job_arrival j + R))).sum ≤
        (l.map (fun tsk_R => W task_cost task_period tsk_R.1 tsk_R.2 R)).sum by
      exact h hp_bounds h_not
    intro l hl
    induction l with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      apply Nat.add_le_add
      · exact hl hd.1 hd.2 (List.mem_cons.mpr (Or.inl rfl))
      · exact ih (fun tsk_k R_k hmem => hl tsk_k R_k (List.mem_cons.mpr (Or.inr hmem)))
  exact Nat.not_lt.mpr h_le h_sum

end DerivingContradiction

end Lemmas

include H_sporadic_tasks H_valid_job_parameters H_valid_task_parameters
  H_constrained_deadlines H_all_jobs_from_taskset
  H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_at_least_one_cpu
  H_work_conserving H_respects_FP_policy
  H_response_time_of_interfering_tasks_is_known
  H_hp_bounds_has_interfering_tasks
  H_response_time_recurrence_holds
  H_response_time_no_larger_than_deadline
  task_in_ts in
theorem bertogna_cirinei_response_time_bound_fp :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
  unfold is_response_time_bound_of_task
  intro j h_arrives h_job_tsk
  -- Strong induction on ctime = job_arrival j + R
  suffices h_ind : ∀ (n : ℕ) (j' : Job),
      arrives_in arr_seq j' → job_task j' = tsk →
      job_arrival j' + R ≤ n →
      completed job_cost sched j' (job_arrival j' + R) by
    exact h_ind (job_arrival j + R + 1) j h_arrives h_job_tsk (Nat.le_succ _)
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j' h_arr' h_tsk' h_le_n
    by_contra h_not_comp
    have h_prev : ∀ j0, arrives_in arr_seq j0 → job_task j0 = tsk →
        job_arrival j0 < job_arrival j' → completed job_cost sched j0 (job_arrival j0 + R) := by
      intro j0 h0_arr h0_tsk h0_lt
      have h_lt_n : job_arrival j0 + R < n := Nat.lt_of_lt_of_le (Nat.add_lt_add_right h0_lt R) h_le_n
      exact ih (job_arrival j0 + R) h_lt_n j0 h0_arr h0_tsk (le_refl _)
    have h_ex := bertogna_fp_exists_task_that_exceeds_bound task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts
      H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      higher_eq_priority H_work_conserving H_respects_FP_policy H_at_least_one_cpu tsk
      hp_bounds H_hp_bounds_has_interfering_tasks R H_response_time_recurrence_holds
      H_response_time_no_larger_than_deadline j' h_arr' h_tsk' h_not_comp h_prev
    obtain ⟨tsk_k, R_k, h_in_bounds, h_exceeds⟩ := h_ex
    have h_bound := bertogna_fp_workload_bounds_interference task_cost task_period task_deadline
      job_arrival job_cost job_deadline job_task arr_seq H_sporadic_tasks H_valid_job_parameters ts
      H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset sched
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      tsk hp_bounds H_response_time_of_interfering_tasks_is_known R j' h_arr' h_tsk'
      tsk_k R_k h_in_bounds
    exact Nat.not_lt.mpr h_bound h_exceeds

end ResponseTimeBound

end ResponseTimeAnalysisFP

end Prosa.Classic.Analysis.Global.Parallel.Bertogna_fp_theory
