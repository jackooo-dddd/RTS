-- Translated from: ../rt-proofs/classic/analysis/uni/basic/fp_rta_comp.v
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp
import Prosa.Classic.Analysis.Uni.Basic.Fp_rta_theory
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Util.Fixedpoint
import Prosa.Classic.Util.Notation

namespace Prosa.Classic.Analysis.Uni.Basic.Fp_rta_comp

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform
open Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp
open Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp.WorkloadBoundFP
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Schedule.Uni.Schedulability hiding schedule scheduled_at service_at service_during service completed_by completed_jobs_dont_execute completion_monotonic
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Util.Fixedpoint
open Prosa.Classic.Util.Notation

namespace ResponseTimeIterationFP

abbrev task_with_response_time (SporadicTask : Type _) := SporadicTask × Time

def max_steps {SporadicTask : Type _} (task_cost : SporadicTask → Time)
    (task_deadline : SporadicTask → Time) (tsk : SporadicTask) : ℕ :=
  task_deadline tsk - task_cost tsk + 1

def per_task_rta {SporadicTask : Type _} [DecidableEq SporadicTask]
    (task_cost : SporadicTask → Time)
    (task_period : SporadicTask → Time)
    (task_deadline : SporadicTask → Time)
    (higher_eq_priority : FP_policy SporadicTask)
    (ts : List SporadicTask) (tsk : SporadicTask) : Option Time :=
  iter_fixpoint (total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk)
    (max_steps task_cost task_deadline tsk) (task_cost tsk)

private def is_valid_bound {SporadicTask : Type _}
    (task_deadline : SporadicTask → Time)
    (tsk_R : SporadicTask × Option Time) : Option (SporadicTask × Time) :=
  match tsk_R with
  | (tsk, some R) =>
    if R ≤ task_deadline tsk then some (tsk, R)
    else none
  | (_, none) => none

def fp_claimed_bounds {SporadicTask : Type _} [DecidableEq SporadicTask]
    (task_cost : SporadicTask → Time)
    (task_period : SporadicTask → Time)
    (task_deadline : SporadicTask → Time)
    (higher_eq_priority : FP_policy SporadicTask)
    (ts : List SporadicTask) : Option (List (task_with_response_time SporadicTask)) :=
  let possible_bounds := ts.map (fun tsk => (tsk, per_task_rta task_cost task_period task_deadline higher_eq_priority ts tsk))
  if possible_bounds.all (fun b => (is_valid_bound task_deadline b).isSome) then
    some (possible_bounds.filterMap (is_valid_bound task_deadline))
  else none

def fp_schedulable {SporadicTask : Type _} [DecidableEq SporadicTask]
    (task_cost : SporadicTask → Time)
    (task_period : SporadicTask → Time)
    (task_deadline : SporadicTask → Time)
    (higher_eq_priority : FP_policy SporadicTask)
    (ts : List SporadicTask) : Prop :=
  fp_claimed_bounds task_cost task_period task_deadline higher_eq_priority ts ≠ none

section Lemmas

  variable {SporadicTask : Type _} [DecidableEq SporadicTask]
  variable (task_cost : SporadicTask → Time)
  variable (task_period : SporadicTask → Time)
  variable (task_deadline : SporadicTask → Time)
  variable (higher_eq_priority : FP_policy SporadicTask)

  variable (ts : List SporadicTask)
  variable (rt_bounds : List (task_with_response_time SporadicTask))
  variable (H_analysis_succeeds :
    fp_claimed_bounds task_cost task_period task_deadline higher_eq_priority ts = some rt_bounds)

  section BoundExists

    variable (tsk : SporadicTask)
    variable (H_tsk_in_ts : tsk ∈ ts)

    include H_analysis_succeeds H_tsk_in_ts

    theorem fp_claimed_bounds_for_every_task :
        ∃ R, (tsk, R) ∈ rt_bounds := by
      simp only [fp_claimed_bounds] at H_analysis_succeeds
      set possible_bounds := ts.map (fun tsk => (tsk, per_task_rta task_cost task_period task_deadline higher_eq_priority ts tsk)) with h_pb
      by_cases h_all : (possible_bounds.all (fun b => (is_valid_bound task_deadline b).isSome)) = true
      · simp [h_all] at H_analysis_succeeds
        have h_in_map : (tsk, per_task_rta task_cost task_period task_deadline higher_eq_priority ts tsk) ∈ possible_bounds := by
          rw [h_pb]; simp only [List.mem_map]
          exact ⟨tsk, H_tsk_in_ts, rfl⟩
        -- From List.all, every element satisfies the predicate
        have h_all_mem : ∀ x ∈ possible_bounds, (is_valid_bound task_deadline x).isSome = true :=
          List.all_eq_true.mp h_all
        have h_valid := h_all_mem _ h_in_map
        -- Case split on per_task_rta result
        cases h_rta : per_task_rta task_cost task_period task_deadline higher_eq_priority ts tsk with
        | none =>
          simp [is_valid_bound, h_rta] at h_valid
        | some R =>
          -- Now is_valid_bound checks R ≤ task_deadline tsk
          by_cases h_le : R ≤ task_deadline tsk
          · exists R
            rw [← H_analysis_succeeds]
            rw [List.mem_filterMap]
            refine ⟨(tsk, per_task_rta task_cost task_period task_deadline higher_eq_priority ts tsk), h_in_map, ?_⟩
            simp [is_valid_bound, h_rta, h_le]
          · exfalso
            simp [is_valid_bound, h_rta, h_le] at h_valid
      · simp [h_all] at H_analysis_succeeds

  end BoundExists

  section PropertiesOfBound

    variable (tsk : SporadicTask)
    variable (R : Time)
    variable (H_tsk_R_computed : (tsk, R) ∈ rt_bounds)

    include H_analysis_succeeds H_tsk_R_computed

    theorem fp_claimed_bounds_from_taskset :
        tsk ∈ ts := by
      simp only [fp_claimed_bounds] at H_analysis_succeeds
      set possible_bounds := ts.map (fun tsk => (tsk, per_task_rta task_cost task_period task_deadline higher_eq_priority ts tsk)) with h_pb
      by_cases h_all : (possible_bounds.all (fun b => (is_valid_bound task_deadline b).isSome)) = true
      · simp [h_all] at H_analysis_succeeds
        rw [← H_analysis_succeeds] at H_tsk_R_computed
        simp only [List.mem_filterMap] at H_tsk_R_computed
        obtain ⟨⟨tsk', optR'⟩, h_mem, h_valid⟩ := H_tsk_R_computed
        simp only [is_valid_bound] at h_valid
        cases optR' with
        | none => simp at h_valid
        | some R' =>
          by_cases h_le : R' ≤ task_deadline tsk'
          · simp [h_le] at h_valid
            obtain ⟨h_tsk_eq, _⟩ := h_valid
            subst h_tsk_eq
            rw [h_pb] at h_mem
            simp only [List.mem_map] at h_mem
            obtain ⟨tsk'', h_in_ts, h_eq'⟩ := h_mem
            exact (Prod.mk.inj h_eq').1 ▸ h_in_ts
          · simp [h_le] at h_valid
      · simp [h_all] at H_analysis_succeeds

    theorem fp_claimed_bounds_computes_iteration :
        per_task_rta task_cost task_period task_deadline higher_eq_priority ts tsk = some R := by
      simp only [fp_claimed_bounds] at H_analysis_succeeds
      set possible_bounds := ts.map (fun t => (t, per_task_rta task_cost task_period task_deadline higher_eq_priority ts t)) with h_pb
      by_cases h_all : (possible_bounds.all (fun b => (is_valid_bound task_deadline b).isSome)) = true
      · simp [h_all] at H_analysis_succeeds
        rw [← H_analysis_succeeds] at H_tsk_R_computed
        simp only [List.mem_filterMap] at H_tsk_R_computed
        obtain ⟨⟨tsk', optR'⟩, h_mem, h_valid⟩ := H_tsk_R_computed
        simp only [is_valid_bound] at h_valid
        cases optR' with
        | none => simp at h_valid
        | some R' =>
          by_cases h_le : R' ≤ task_deadline tsk'
          · simp [h_le] at h_valid
            obtain ⟨h_tsk_eq, h_R_eq⟩ := h_valid
            subst h_tsk_eq; subst h_R_eq
            rw [h_pb] at h_mem
            simp only [List.mem_map] at h_mem
            obtain ⟨t'', h_in_ts, h_eq'⟩ := h_mem
            have h_parts := Prod.mk.inj h_eq'
            rw [← h_parts.1]
            exact h_parts.2
          · simp [h_le] at h_valid
      · simp [h_all] at H_analysis_succeeds

    theorem fp_claimed_bounds_yields_fixed_point :
        R = total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk R := by
      have h_iter := fp_claimed_bounds_computes_iteration task_cost task_period task_deadline
        higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
      unfold per_task_rta at h_iter
      have h_cases := iter_fixpoint_cases
        (total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk)
        (max_steps task_cost task_deadline tsk)
        (task_cost tsk)
      cases h_cases with
      | inl h_none => rw [h_none] at h_iter; exact absurd h_iter (by simp)
      | inr h_some =>
        obtain ⟨y, h_eq, h_fp⟩ := h_some
        rw [h_eq] at h_iter
        have h_Ry : y = R := Option.some_injective _ h_iter
        subst h_Ry
        exact h_fp

    theorem fp_claimed_bounds_le_deadline :
        R ≤ task_deadline tsk := by
      simp only [fp_claimed_bounds] at H_analysis_succeeds
      set possible_bounds := ts.map (fun tsk => (tsk, per_task_rta task_cost task_period task_deadline higher_eq_priority ts tsk)) with h_pb
      by_cases h_all : (possible_bounds.all (fun b => (is_valid_bound task_deadline b).isSome)) = true
      · simp [h_all] at H_analysis_succeeds
        rw [← H_analysis_succeeds] at H_tsk_R_computed
        simp only [List.mem_filterMap] at H_tsk_R_computed
        obtain ⟨⟨tsk', optR'⟩, h_mem, h_valid⟩ := H_tsk_R_computed
        simp only [is_valid_bound] at h_valid
        cases optR' with
        | none => simp at h_valid
        | some R' =>
          by_cases h_le : R' ≤ task_deadline tsk'
          · simp [h_le] at h_valid
            obtain ⟨h_tsk_eq, h_R_eq⟩ := h_valid
            subst h_tsk_eq; subst h_R_eq
            exact h_le
          · simp [h_le] at h_valid
      · simp [h_all] at H_analysis_succeeds

    section BoundPositive

      variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
      variable (H_cost_positive : task_cost tsk > 0)
      variable (H_period_positive : ∀ tsk, tsk ∈ ts → task_period tsk > 0)

      include H_priority_is_reflexive H_cost_positive H_period_positive

      theorem fp_claimed_bounds_gt_zero :
          R > 0 := by
        -- R is obtained from iter_fixpoint, and we need to show R ≥ task_cost tsk ≥ 1
        -- Strategy: R ≥ task_cost tsk > 0 using iter_fixpoint_ge_bottom
        have h_iter := fp_claimed_bounds_computes_iteration task_cost task_period task_deadline
          higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
        have h_tsk_in := fp_claimed_bounds_from_taskset task_cost task_period task_deadline
          higher_eq_priority ts rt_bounds H_analysis_succeeds tsk R H_tsk_R_computed
        -- The workload bound is ≥ task_cost tsk
        have h_ge : total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk (task_cost tsk) ≥ task_cost tsk :=
          total_workload_bound_fp_ge_cost task_cost task_period higher_eq_priority ts tsk
            h_tsk_in H_priority_is_reflexive H_cost_positive
            (H_period_positive tsk h_tsk_in)
        -- The workload bound is monotone
        have h_mon : Prosa.Classic.Util.Fixedpoint.monotone
          (total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk)
          (· ≤ ·) := by
          intro x1 x2 h_le
          exact total_workload_bound_fp_non_decreasing task_cost task_period higher_eq_priority ts tsk
            (fun t ht => H_period_positive t ht) x1 x2 h_le
        -- Use iter_fixpoint_ge_bottom
        unfold per_task_rta at h_iter
        have h_bottom := @iter_fixpoint_ge_bottom _ _
          (total_workload_bound_fp task_cost task_period higher_eq_priority ts tsk)
          (· ≤ ·)
          (fun x => le_refl x)
          (fun x y z hxy hyz => le_trans hxy hyz)
          h_mon
          (max_steps task_cost task_deadline tsk)
          (task_cost tsk)
          R
          h_iter
          h_ge
        exact lt_of_lt_of_le H_cost_positive h_bottom

    end BoundPositive

  end PropertiesOfBound

end Lemmas

section ProvingCorrectness

  variable {SporadicTask : Type _} [DecidableEq SporadicTask]
  variable (task_cost : SporadicTask → Time)
  variable (task_period : SporadicTask → Time)
  variable (task_deadline : SporadicTask → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_deadline : Job → Time)
  variable (job_task : Job → SporadicTask)

  variable (ts : List SporadicTask)

  variable (H_valid_task_parameters :
    valid_sporadic_taskset task_cost task_period task_deadline ts)

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
  variable (H_no_duplicate_arrivals : arrival_sequence_is_a_set arr_seq)

  variable (H_all_jobs_from_taskset :
    ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

  variable (H_valid_job_parameters :
    ∀ j,
      arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

  variable (H_sporadic_tasks :
    Prosa.Classic.Analysis.Uni.Basic.Workload_bound_fp.sporadic_task_model
      task_period job_arrival job_task arr_seq)

  variable (higher_eq_priority : FP_policy SporadicTask)

  variable (H_priority_reflexive : FP_is_reflexive higher_eq_priority)
  variable (H_priority_transitive : FP_is_transitive higher_eq_priority)

  variable (sched : schedule Job)
  variable (H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq)

  variable (H_jobs_must_arrive_to_execute :
    jobs_must_arrive_to_execute job_arrival sched)
  variable (H_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost sched)

  variable (H_work_conserving : work_conserving job_arrival job_cost arr_seq sched)
  variable (H_respects_FP_policy :
    respects_FP_policy job_arrival job_cost job_task arr_seq sched higher_eq_priority)

  include H_valid_task_parameters H_arrival_times_are_consistent H_no_duplicate_arrivals
          H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks
          H_priority_reflexive H_priority_transitive
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
          H_completed_jobs_dont_execute H_work_conserving H_respects_FP_policy

  theorem fp_analysis_yields_response_time_bounds :
      ∀ tsk R,
        (match fp_claimed_bounds task_cost task_period task_deadline higher_eq_priority ts with
         | some bounds => (tsk, R) ∈ bounds
         | none => False) →
        Prosa.Classic.Model.Schedule.Uni.Schedulability.is_response_time_bound_of_task
          job_arrival job_cost job_task arr_seq sched tsk R := by
    intro tsk R h_match
    set bounds_opt := fp_claimed_bounds task_cost task_period task_deadline higher_eq_priority ts with h_bounds_def
    cases h_case : bounds_opt with
    | none => rw [h_case] at h_match; exact absurd h_match id
    | some rt_bounds =>
      rw [h_case] at h_match
      -- h_match : (tsk, R) ∈ rt_bounds
      have h_from_ts := fp_claimed_bounds_from_taskset task_cost task_period task_deadline
        higher_eq_priority ts rt_bounds h_case tsk R h_match
      have h_fp := fp_claimed_bounds_yields_fixed_point task_cost task_period task_deadline
        higher_eq_priority ts rt_bounds h_case tsk R h_match
      -- Need R > 0
      have h_valid_params := H_valid_task_parameters
      have h_tsk_valid := h_valid_params tsk h_from_ts
      have h_cost_pos : task_cost tsk > 0 := h_tsk_valid.1
      have h_period_pos : ∀ t, t ∈ ts → task_period t > 0 := fun t ht => (h_valid_params t ht).2.1
      have h_R_gt := fp_claimed_bounds_gt_zero task_cost task_period task_deadline
        higher_eq_priority ts rt_bounds h_case tsk R h_match
        H_priority_reflexive h_cost_pos h_period_pos
      -- Apply the main RTA theorem
      have h_rta := Prosa.Classic.Analysis.Uni.Basic.Fp_rta_theory.ResponseTimeAnalysisFP.uniprocessor_response_time_bound_fp
        task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task
        arr_seq H_arrival_times_are_consistent H_no_duplicate_arrivals
        H_sporadic_tasks H_valid_job_parameters
        ts H_valid_task_parameters H_all_jobs_from_taskset
        sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        higher_eq_priority H_priority_reflexive H_priority_transitive
        H_work_conserving H_respects_FP_policy
        tsk h_from_ts R h_R_gt h_fp
      -- h_rta : ResponseTime.is_response_time_bound_of_task ... (uses Schedule.completed_by)
      -- goal : Schedulability.is_response_time_bound_of_task ... (uses Schedulability.completed_by)
      -- Bridge the two definitions
      intro j h_arrives h_task
      have h_bound := h_rta j h_arrives h_task
      -- h_bound : Schedule.completed_by job_cost sched j (job_arrival j + R)
      -- goal : Schedulability.completed_by job_cost sched j (job_arrival j + R)
      show Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_by job_cost sched j (job_arrival j + R)
      unfold Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_by
        Prosa.Classic.Model.Schedule.Uni.Schedulability.service
        Prosa.Classic.Model.Schedule.Uni.Schedulability.service_during
        Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at
        Prosa.Classic.Model.Schedule.Uni.Schedulability.scheduled_at
      show job_cost j ≤ ∑ t ∈ Finset.Ico 0 (job_arrival j + R),
        if (sched t == some j) = true then 1 else 0
      unfold Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime.is_response_time_bound_of_job
        Prosa.Classic.Model.Schedule.Uni.Schedule.completed_by
        Prosa.Classic.Model.Schedule.Uni.Schedule.service
        Prosa.Classic.Model.Schedule.Uni.Schedule.service_during
        Prosa.Classic.Model.Schedule.Uni.Schedule.service_at
        Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at at h_bound
      calc job_cost j
          ≤ ∑ t ∈ Finset.Ico 0 (job_arrival j + R),
              (sched t == some j).toNat := h_bound
        _ = ∑ t ∈ Finset.Ico 0 (job_arrival j + R),
              (if (sched t == some j) = true then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro t _
            cases (sched t == some j) <;> simp

  section AnalysisIsSufficient

    variable (H_test_succeeds : fp_schedulable task_cost task_period task_deadline higher_eq_priority ts)

    include H_test_succeeds

    theorem taskset_schedulable_by_fp_rta :
        ∀ tsk, tsk ∈ ts →
          task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
      intro tsk h_in
      have h_test := H_test_succeeds
      -- fp_schedulable means fp_claimed_bounds ≠ none
      unfold fp_schedulable at h_test
      -- Extract the rt_bounds
      cases h_case : fp_claimed_bounds task_cost task_period task_deadline higher_eq_priority ts with
      | none => exact absurd h_case h_test
      | some rt_bounds =>
        obtain ⟨R, h_R_in⟩ := fp_claimed_bounds_for_every_task task_cost task_period task_deadline
          higher_eq_priority ts rt_bounds h_case tsk h_in
        have h_le := fp_claimed_bounds_le_deadline task_cost task_period task_deadline
          higher_eq_priority ts rt_bounds h_case tsk R h_R_in
        have h_match : (match fp_claimed_bounds task_cost task_period task_deadline higher_eq_priority ts with
           | some bounds => (tsk, R) ∈ bounds
           | none => False) := by rw [h_case]; exact h_R_in
        have h_bound := fp_analysis_yields_response_time_bounds task_cost task_period task_deadline
          job_arrival job_cost job_deadline job_task ts H_valid_task_parameters arr_seq
          H_arrival_times_are_consistent H_no_duplicate_arrivals H_all_jobs_from_taskset
          H_valid_job_parameters H_sporadic_tasks higher_eq_priority H_priority_reflexive
          H_priority_transitive sched H_jobs_come_from_arrival_sequence
          H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
          H_respects_FP_policy tsk R h_match
        -- Now apply task_completes_before_deadline
        -- Need H_job_deadline_eq_task_deadline
        have h_jd_eq : ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j) := by
          intro j h_arr
          exact (H_valid_job_parameters j h_arr).2.2
        -- Need completed_jobs_dont_execute in the Schedulability sense
        have h_cjde : Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_jobs_dont_execute job_cost sched := by
          intro j t
          have h1 := H_completed_jobs_dont_execute j t
          show Prosa.Classic.Model.Schedule.Uni.Schedulability.service sched j t ≤ job_cost j
          have h_serv : Prosa.Classic.Model.Schedule.Uni.Schedule.service sched j t =
                        Prosa.Classic.Model.Schedule.Uni.Schedulability.service sched j t := by
            unfold Prosa.Classic.Model.Schedule.Uni.Schedule.service Prosa.Classic.Model.Schedule.Uni.Schedulability.service
            unfold Prosa.Classic.Model.Schedule.Uni.Schedule.service_during Prosa.Classic.Model.Schedule.Uni.Schedulability.service_during
            congr 1; ext t'
            unfold Prosa.Classic.Model.Schedule.Uni.Schedule.service_at Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at
            unfold Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at Prosa.Classic.Model.Schedule.Uni.Schedulability.scheduled_at
            simp [Bool.toNat, beq_iff_eq]
          rw [← h_serv]; exact h1
        exact Prosa.Classic.Model.Schedule.Uni.Schedulability.task_completes_before_deadline
          job_arrival job_cost job_deadline job_task arr_seq sched task_deadline h_jd_eq h_cjde tsk R h_le h_bound

    theorem jobs_schedulable_by_fp_rta :
        ∀ j,
          arrives_in arr_seq j →
          job_misses_no_deadline job_arrival job_cost job_deadline sched j := by
      intro j h_arr
      have h_sched := taskset_schedulable_by_fp_rta task_cost task_period task_deadline
        job_arrival job_cost job_deadline job_task ts H_valid_task_parameters arr_seq
        H_arrival_times_are_consistent H_no_duplicate_arrivals H_all_jobs_from_taskset
        H_valid_job_parameters H_sporadic_tasks higher_eq_priority H_priority_reflexive
        H_priority_transitive sched H_jobs_come_from_arrival_sequence
        H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
        H_respects_FP_policy H_test_succeeds
      exact h_sched (job_task j) (H_all_jobs_from_taskset j h_arr) j h_arr rfl

  end AnalysisIsSufficient

end ProvingCorrectness

end ResponseTimeIterationFP

end Prosa.Classic.Analysis.Uni.Basic.Fp_rta_comp
