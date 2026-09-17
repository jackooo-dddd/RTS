-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/fixed_priority/nonpr_reg/concrete_models/response_time_bound.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
import Prosa.Classic.Model.Arrival.Curves.Bounds
import Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions
import Prosa.Classic.Model.Schedule.Uni.Basic.Platform
import Prosa.Classic.Model.Priority
import Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound
import Prosa.Util.Epsilon
import Prosa.Util.Nondecreasing
import Prosa.Classic.Model.Schedule.Uni.Limited.Fixed_priority.Response_time_bound
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Fixed_priority.Nonpr_reg.Concrete_models.Response_time_bound

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Curves.Bounds.ArrivalCurves
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Limited.Platform.Definitions.LimitedPreemptionPlatform
open Prosa.Classic.Model.Schedule.Uni.Limited.Schedule
open Prosa.Classic.Model.Schedule.Uni.Nonpreemptive.Schedule
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Uni.Arrival_curves.Workload_bound.MaxArrivalsWorkloadBound
open Prosa.Util.Epsilon
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Util.Nondecreasing
open Prosa.Util.List
open Prosa.Classic.Model.Schedule.Uni.Limited.Busy_interval.BusyIntervalJLFP
open Prosa.Classic.Model.Arrival.Basic.Job

namespace ModelWithLimitedPreemptions

variable {Task : Type _} [DecidableEq Task]
variable (task_cost : Task → Time)

variable {Job : Type _} [DecidableEq Job]
variable (job_cost : Job → Time)
variable (job_task : Job → Task)

variable (arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence Job)
variable (job_preemption_points : Job → List Time)

def lengths_of_segments (j : Job) : List Nat := distances (job_preemption_points j)

def job_max_nps (j : Job) : Nat := max0 (lengths_of_segments job_preemption_points j)

def job_last_nps (j : Job) : Nat := last0 (lengths_of_segments job_preemption_points j)

variable (task_preemption_points : Task → List Time)

def task_last_nps (tsk : Task) : Nat := last0 (distances (task_preemption_points tsk))

def task_max_nps (tsk : Task) : Nat := max0 (distances (task_preemption_points tsk))

def limited_preemptions_job_model : Prop :=
  (∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    job_cost j = 0 → job_preemption_points j = [0, 0]) ∧
  (∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    job_cost j > 0 → job_last_nps job_preemption_points j > 0) ∧
  (∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    first0 (job_preemption_points j) = 0) ∧
  (∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    last0 (job_preemption_points j) = job_cost j) ∧
  (∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    nondecreasing_sequence (job_preemption_points j))

variable (ts : List Task)

def fixed_preemption_points_model : Prop :=
  limited_preemptions_job_model job_cost arr_seq job_preemption_points ∧
  (∀ tsk, tsk ∈ ts → first0 (task_preemption_points tsk) = 0) ∧
  (∀ tsk, tsk ∈ ts → last0 (task_preemption_points tsk) = task_cost tsk) ∧
  (∀ tsk, tsk ∈ ts → nondecreasing_sequence (task_preemption_points tsk)) ∧
  (∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    (job_preemption_points j).length = (task_preemption_points (job_task j)).length) ∧
  (∀ j n, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    (distances (job_preemption_points j)).getD n 0 ≤
    (distances (task_preemption_points (job_task j))).getD n 0) ∧
  (∀ tsk n, tsk ∈ ts →
    n < (distances (task_preemption_points tsk)).length →
    ε ≤ (distances (task_preemption_points tsk)).getD n 0)

variable (task_max_nps_f : Task → Time)

def model_with_floating_nonpreemptive_regions : Prop :=
  limited_preemptions_job_model job_cost arr_seq job_preemption_points ∧
  (∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    job_max_nps job_preemption_points j ≤ task_max_nps_f (job_task j))

def can_be_preempted_for_model_with_limited_preemptions (j : Job) (progr : Time) : Bool :=
  decide (progr ∈ job_preemption_points j)

def is_schedule_with_limited_preemptions (sched : schedule Job) : Prop :=
  ∀ j t,
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j →
    can_be_preempted_for_model_with_limited_preemptions job_preemption_points j
      (service sched j t) = false →
    scheduled_at sched j t = true

end ModelWithLimitedPreemptions

namespace RTAforConcreteModels

section Analysis

  variable {Task : Type _} [DecidableEq Task]
  variable (task_cost : Task → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_task : Job → Task)

  variable (arr_seq : Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence Job)
  variable (H_arrival_times_are_consistent :
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_times_are_consistent job_arrival arr_seq)
  variable (H_arr_seq_is_a_set :
    Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrival_sequence_is_a_set arr_seq)

  variable (ts : List Task)

  variable (H_all_jobs_from_taskset :
    ∀ j, Prosa.Classic.Model.Arrival.Basic.Arrival_sequence.arrives_in arr_seq j → job_task j ∈ ts)

  variable (H_job_cost_le_task_cost :
    Prosa.Classic.Model.Arrival.Basic.Job.cost_of_jobs_from_arrival_sequence_le_task_cost
      task_cost job_cost job_task arr_seq)

  variable (max_arrivals : Task → Time → Nat)
  variable (H_family_of_proper_arrival_curves :
    family_of_proper_arrival_curves job_task arr_seq max_arrivals ts)

  variable (tsk : Task)
  variable (H_tsk_in_ts : tsk ∈ ts)

  variable (sched : schedule Job)
  variable (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)

  variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
  variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)

  variable (H_work_conserving :
    Prosa.Classic.Model.Schedule.Uni.Basic.Platform.Platform.work_conserving
      job_arrival job_cost arr_seq sched)

  variable (H_sequential_jobs : sequential_jobs job_arrival job_cost sched job_task)

  variable (higher_eq_priority : FP_policy Task)
  variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
  variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)

  section RTAforFullyPreemptiveFPModelwithArrivalCurves

    variable (H_respects_policy_preemptive :
      respects_FP_policy_at_preemption_point
        job_arrival job_cost job_task arr_seq sched
        (fun _j _prog => true) higher_eq_priority)

    variable (L : Time)
    variable (H_L_positive : L > 0)
    variable (H_fixed_point_preemptive :
      L = total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L)

    variable (R : Nat)
    variable (H_R_is_maximum_preemptive :
      ∀ A,
        A < L ∧ task_request_bound_function task_cost max_arrivals tsk A ≠
          task_request_bound_function task_cost max_arrivals tsk (A + ε) →
        ∃ F,
          A + F = task_request_bound_function task_cost max_arrivals tsk (A + ε) +
                  total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F) ∧
          F ≤ R)

    variable (H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched
        (FP_to_JLFP job_task higher_eq_priority) tsk 0)

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset
      H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive
      H_respects_policy_preemptive H_L_positive H_fixed_point_preemptive H_R_is_maximum_preemptive H_priority_inversion_is_bounded in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive H_respects_policy_preemptive H_L_positive H_fixed_point_preemptive H_R_is_maximum_preemptive H_priority_inversion_is_bounded in
    theorem uniprocessor_response_time_bound_fully_preemptive_fp :
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
      apply Prosa.Classic.Model.Schedule.Uni.Limited.Fixed_priority.Response_time_bound.AbstractRTAforFPwithArrivalCurves.uniprocessor_response_time_bound_fp
        task_cost job_arrival job_cost job_task arr_seq
        H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
        max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
        (fun j => job_cost j) (fun t => task_cost t)
        -- proper_job_lock_in_service
        ⟨fun j hARR hPOS => hPOS,
         fun j hARR hPOS => Nat.le_refl _,
         fun j t t' hARR hLE hSERV hNCOMPL =>
           -- If service j t ≥ job_cost j, then completed_by j t, contradiction
           -- service ≥ lock_in = job_cost means completed, but hNCOMPL says not completed at t'
           -- Actually lock_in = job_cost, so service ≥ job_cost means completed by t
           -- Then by monotonicity, completed by t', contradicting hNCOMPL
           absurd (Prosa.Classic.Model.Schedule.Uni.Schedule.completion_monotonic job_cost sched j t t' hLE
             (by simp only [completed_by]; omega)) hNCOMPL⟩
        -- proper_task_lock_in_service
        ⟨Nat.le_refl _,
         fun j hARR hTSK => by rw [← hTSK]; exact H_job_cost_le_task_cost j hARR⟩
        higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive
        0 -- priority_inversion_bound = 0
        H_priority_inversion_is_bounded
        L H_L_positive
        (by simp only [Time] at *; omega) -- H_fixed_point: L = 0 + total_hep_rbf L
        R
        (fun A hA => by
          obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum_preemptive A hA
          exact ⟨F, by simp only [Time] at *; omega, by simp only [Time] at *; omega⟩)

  end RTAforFullyPreemptiveFPModelwithArrivalCurves

  section RTAforFullyNonPreemptiveFPModelwithArrivalCurves

    variable (H_nonpreemptive_sched : is_nonpreemptive_schedule job_cost sched)

    variable (H_respects_policy_nonpreemptive :
      respects_FP_policy_at_preemption_point
        job_arrival job_cost job_task arr_seq sched
        (fun j prog => decide (prog = 0 ∨ job_cost j ≤ prog)) higher_eq_priority)

    private noncomputable def blocking_bound_nonpreemptive : Nat :=
      ((ts.filter (fun tsk_other => !higher_eq_priority tsk_other tsk)).map
        (fun tsk_other => task_cost tsk_other - ε)).foldl max 0

    variable (L : Time)
    variable (H_L_positive : L > 0)
    variable (H_fixed_point_nonpreemptive :
      L = blocking_bound_nonpreemptive task_cost ts tsk higher_eq_priority +
          total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L)

    variable (R : Nat)
    variable (H_R_is_maximum_nonpreemptive :
      ∀ A,
        A < L ∧ task_request_bound_function task_cost max_arrivals tsk A ≠
          task_request_bound_function task_cost max_arrivals tsk (A + ε) →
        ∃ F,
          A + F = blocking_bound_nonpreemptive task_cost ts tsk higher_eq_priority
                  + (task_request_bound_function task_cost max_arrivals tsk (A + ε) - (task_cost tsk - ε))
                  + total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F) ∧
          F + (task_cost tsk - ε) ≤ R)

    variable (H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched
        (FP_to_JLFP job_task higher_eq_priority) tsk
        (blocking_bound_nonpreemptive task_cost ts tsk higher_eq_priority))

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset
      H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive
      H_nonpreemptive_sched H_respects_policy_nonpreemptive
      H_L_positive H_fixed_point_nonpreemptive H_R_is_maximum_nonpreemptive H_priority_inversion_is_bounded in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive H_nonpreemptive_sched H_respects_policy_nonpreemptive H_L_positive H_fixed_point_nonpreemptive H_R_is_maximum_nonpreemptive H_priority_inversion_is_bounded in
    theorem uniprocessor_response_time_bound_fully_nonpreemptive_fp :
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
      -- Handle zero-cost task
      by_cases hTSK_POS : task_cost tsk > 0
      · apply Prosa.Classic.Model.Schedule.Uni.Limited.Fixed_priority.Response_time_bound.AbstractRTAforFPwithArrivalCurves.uniprocessor_response_time_bound_fp
          task_cost job_arrival job_cost job_task arr_seq
          H_arrival_times_are_consistent H_arr_seq_is_a_set sched
          H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
          H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
          max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
          (fun _j => ε) (fun _tsk => ε) -- lock-in service = ε
          -- proper_job_lock_in_service
          ⟨fun j _hARR _hPOS => by simp [ε],
           fun j _hARR hPOS => hPOS,
           fun j t t' hARR hLE hSERV hNCOMPL => by
             have hSERV' : 0 < service sched j t := hSERV
             unfold service at hSERV'
             have := incremental_service_during sched j 0 t 0 hSERV'
             obtain ⟨t₀, ht₀_ge, ht₀_lt, hSCHED₀, _⟩ := this
             exact H_nonpreemptive_sched j t₀ t' (ht₀_lt.le.trans hLE) hSCHED₀ hNCOMPL⟩
          -- proper_task_lock_in_service
          ⟨hTSK_POS, fun j _hARR _hTSK => le_refl _⟩
          higher_eq_priority H_priority_is_reflexive
          H_priority_is_transitive
          (blocking_bound_nonpreemptive task_cost ts tsk higher_eq_priority)
          H_priority_inversion_is_bounded
          L H_L_positive H_fixed_point_nonpreemptive R
          (fun A hA => by
            obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum_nonpreemptive A hA
            exact ⟨F, by simp only [ε, Time] at *; omega, hLE⟩)
      · -- Zero-cost task: all jobs have zero cost
        have hTSK_ZERO : task_cost tsk = 0 := by
          rcases Nat.eq_zero_or_pos (task_cost tsk) with h | h
          · exact h
          · exact absurd h hTSK_POS
        intro j hARR hTSK
        have hJ_ZERO : job_cost j = 0 := by
          have hCOST : job_cost j ≤ task_cost (job_task j) := H_job_cost_le_task_cost j hARR
          rw [hTSK, hTSK_ZERO] at hCOST
          exact Nat.le_zero.mp hCOST
        unfold is_response_time_bound_of_job completed_by; rw [hJ_ZERO]; exact Nat.zero_le _

  end RTAforFullyNonPreemptiveFPModelwithArrivalCurves

  section RTAforFixedPreemptionPointsModelwithArrivalCurves

    variable (job_preemption_points : Job → List Time)
    variable (task_preemption_points : Task → List Time)
    variable (H_model_with_fixed_preemption_points :
      ModelWithLimitedPreemptions.fixed_preemption_points_model
        task_cost job_cost job_task arr_seq
        job_preemption_points task_preemption_points ts)

    variable (H_schedule_with_limited_preemptions :
      ModelWithLimitedPreemptions.is_schedule_with_limited_preemptions
        arr_seq job_preemption_points sched)

    variable (H_respects_policy_fixed :
      respects_FP_policy_at_preemption_point
        job_arrival job_cost job_task arr_seq sched
        (ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
          job_preemption_points) higher_eq_priority)

    private noncomputable def blocking_bound_fixed : Nat :=
      ((ts.filter (fun tsk_other => !higher_eq_priority tsk_other tsk)).map
        (fun tsk_other =>
          ModelWithLimitedPreemptions.task_max_nps task_preemption_points tsk_other - ε)).foldl max 0

    variable (L : Time)
    variable (H_L_positive : L > 0)
    variable (H_fixed_point_fixed :
      L = blocking_bound_fixed ts tsk higher_eq_priority task_preemption_points +
          total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L)

    variable (R : Nat)
    variable (H_R_is_maximum_fixed :
      ∀ A,
        A < L ∧ task_request_bound_function task_cost max_arrivals tsk A ≠
          task_request_bound_function task_cost max_arrivals tsk (A + ε) →
        ∃ F,
          A + F = blocking_bound_fixed ts tsk higher_eq_priority task_preemption_points
                  + (task_request_bound_function task_cost max_arrivals tsk (A + ε) -
                     (ModelWithLimitedPreemptions.task_last_nps task_preemption_points tsk - ε))
                  + total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F) ∧
          F + (ModelWithLimitedPreemptions.task_last_nps task_preemption_points tsk - ε) ≤ R)

    variable (H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched
        (FP_to_JLFP job_task higher_eq_priority) tsk
        (blocking_bound_fixed ts tsk higher_eq_priority task_preemption_points))

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset
      H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive
      H_model_with_fixed_preemption_points H_schedule_with_limited_preemptions
      H_respects_policy_fixed H_L_positive H_fixed_point_fixed H_R_is_maximum_fixed H_priority_inversion_is_bounded in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive H_model_with_fixed_preemption_points H_schedule_with_limited_preemptions H_respects_policy_fixed H_L_positive H_fixed_point_fixed H_R_is_maximum_fixed H_priority_inversion_is_bounded in
    theorem uniprocessor_response_time_bound_fp_with_fixed_preemption_points :
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
      apply Prosa.Classic.Model.Schedule.Uni.Limited.Fixed_priority.Response_time_bound.AbstractRTAforFPwithArrivalCurves.uniprocessor_response_time_bound_fp
        task_cost job_arrival job_cost job_task arr_seq
        H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
        max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
        (fun j => job_cost j - (ModelWithLimitedPreemptions.job_last_nps job_preemption_points j - ε))
        (fun t => task_cost t - (ModelWithLimitedPreemptions.task_last_nps task_preemption_points t - ε))
        -- proper_job_lock_in_service
        ⟨fun j hARR hPOS => by
           have hLAST := H_model_with_fixed_preemption_points.1.2.1 j hARR hPOS
           have h_nd_j := H_model_with_fixed_preemption_points.1.2.2.2.2 j hARR
           have h_end_j := H_model_with_fixed_preemption_points.1.2.2.2.1 j hARR
           have h_jlns_le : ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
             le_trans (last_of_seq_le_max_of_seq _)
               (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_j) (le_of_eq h_end_j))
           simp only [Time, ε] at *; omega,
         fun j _hARR _hPOS => Nat.sub_le _ _,
         fun j t t' hARR hLE hSERV hNCOMPL => by
           have h_nd := H_model_with_fixed_preemption_points.1.2.2.2.2 j hARR
           have h_end := H_model_with_fixed_preemption_points.1.2.2.2.1 j hARR
           have h_beg := H_model_with_fixed_preemption_points.1.2.2.1 j hARR
           have hS_lt : service sched j t' < job_cost j := not_le.mp hNCOMPL
           have hS_ge : job_cost j -
               (ModelWithLimitedPreemptions.job_last_nps job_preemption_points j - ε) ≤
               service sched j t' := le_trans hSERV (service_monotonic sched j t t' hLE)
           have hPOS : job_cost j > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hS_lt
           have hLAST_pos := H_model_with_fixed_preemption_points.1.2.1 j hARR hPOS
           have h_jlns_le : ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
             le_trans (last_of_seq_le_max_of_seq _)
               (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd) (le_of_eq h_end))
           have h_len : 2 ≤ (job_preemption_points j).length := by
             by_contra hlt; push_neg at hlt
             have hle1 : (job_preemption_points j).length ≤ 1 := by omega
             have hfe : first0 (job_preemption_points j) = last0 (job_preemption_points j) := by
               cases hq : (job_preemption_points j) with
               | nil => simp [first0, last0, List.headD, List.getLastD]
               | cons a tl =>
                 cases tl with
                 | nil => simp [first0, last0, List.headD, List.getLastD]
                 | cons b rest => simp [hq] at hle1
             rw [h_beg, h_end] at hfe; omega
           have h_lsmd := last_seq_minus_last_distance_seq (job_preemption_points j) h_nd
           rw [h_end] at h_lsmd
           have h_last := last0_nth (job_preemption_points j)
           rw [h_end] at h_last
           have h_len_eq : (job_preemption_points j).length - 2 + 1 =
               (job_preemption_points j).length - 1 := by omega
           have h_jlns_eq : ModelWithLimitedPreemptions.job_last_nps job_preemption_points j =
               last0 (distances (job_preemption_points j)) := rfl
           have h_gt : nthD (job_preemption_points j)
               ((job_preemption_points j).length - 2) < service sched j t' := by
             simp only [h_jlns_eq, Time, ε] at hS_ge hLAST_pos h_jlns_le h_lsmd ⊢; omega
           have h_lt : service sched j t' < nthD (job_preemption_points j)
               ((job_preemption_points j).length - 2 + 1) := by
             rw [h_len_eq, ← h_last]; exact hS_lt
           have h_not_mem := antidensity_of_nondecreasing_seq _ _ _ h_nd ⟨h_gt, h_lt⟩
           have h_cant : ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
               job_preemption_points j (service sched j t') = false := by
             unfold ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
             exact decide_eq_false h_not_mem
           exact H_schedule_with_limited_preemptions j t' hARR h_cant⟩
        -- proper_task_lock_in_service
        ⟨Nat.sub_le _ _,
         fun j hARR hTSK => by
           have hCOST : job_cost j ≤ task_cost (job_task j) := H_job_cost_le_task_cost j hARR
           rw [hTSK] at hCOST
           by_cases hZERO : job_cost j = 0
           · simp only [Time, ε] at *; omega
           · have hPOS : job_cost j > 0 := Nat.pos_of_ne_zero hZERO
             have h_nd_j := H_model_with_fixed_preemption_points.1.2.2.2.2 j hARR
             have h_end_j := H_model_with_fixed_preemption_points.1.2.2.2.1 j hARR
             have h_beg_j := H_model_with_fixed_preemption_points.1.2.2.1 j hARR
             have h_nd_tsk := H_model_with_fixed_preemption_points.2.2.2.1 tsk H_tsk_in_ts
             have h_end_tsk := H_model_with_fixed_preemption_points.2.2.1 tsk H_tsk_in_ts
             have h_beg_tsk := H_model_with_fixed_preemption_points.2.1 tsk H_tsk_in_ts
             have h_same_len := H_model_with_fixed_preemption_points.2.2.2.2.1 j hARR
             have h_dist := H_model_with_fixed_preemption_points.2.2.2.2.2.1 j
             have h_len_j : 2 ≤ (job_preemption_points j).length := by
               by_contra hlt; push_neg at hlt
               have hle1 : (job_preemption_points j).length ≤ 1 := by omega
               have hfe : first0 (job_preemption_points j) = last0 (job_preemption_points j) := by
                 cases hq : (job_preemption_points j) with
                 | nil => simp [first0, last0, List.headD, List.getLastD]
                 | cons a tl =>
                   cases tl with
                   | nil => simp [first0, last0, List.headD, List.getLastD]
                   | cons b rest => simp [hq] at hle1
               rw [h_beg_j, h_end_j] at hfe; simp only [Time] at *; omega
             have h_len_tsk : 2 ≤ (task_preemption_points tsk).length := by
               have hsame := h_same_len; rw [hTSK] at hsame; omega
             have h_lsmd_j := last_seq_minus_last_distance_seq (job_preemption_points j) h_nd_j
             rw [h_end_j] at h_lsmd_j
             have h_lsmd_tsk := last_seq_minus_last_distance_seq (task_preemption_points tsk) h_nd_tsk
             rw [h_end_tsk] at h_lsmd_tsk
             have h_jlns_le : ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
               le_trans (last_of_seq_le_max_of_seq _)
                 (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_j) (le_of_eq h_end_j))
             have h_tlns_le : ModelWithLimitedPreemptions.task_last_nps task_preemption_points tsk ≤ task_cost tsk :=
               le_trans (last_of_seq_le_max_of_seq _)
                 (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_tsk) (le_of_eq h_end_tsk))
             have h_dom := domination_of_distances_implies_domination_of_seq
               (job_preemption_points j) (task_preemption_points tsk)
               (by rw [h_beg_j, h_beg_tsk])
               h_len_j h_len_tsk
               (by rw [h_same_len, hTSK])
               h_nd_j h_nd_tsk
               (fun n => by have := h_dist n hARR; rw [hTSK] at this; exact this)
             have h_len_eq : (job_preemption_points j).length = (task_preemption_points tsk).length := by
               rw [h_same_len, hTSK]
             have h_snd_last := h_dom ((task_preemption_points tsk).length - 2)
             rw [h_len_eq] at h_lsmd_j
             rw [← h_lsmd_j, ← h_lsmd_tsk] at h_snd_last
             have hLAST_pos := H_model_with_fixed_preemption_points.1.2.1 j hARR hPOS
             have h_nonempty := H_model_with_fixed_preemption_points.2.2.2.2.2.2
             have h_dist_len_pos : 0 < (distances (task_preemption_points tsk)).length := by
               have := size_of_seq_of_distances (task_preemption_points tsk) h_len_tsk; omega
             have h_tlns_pos : ε ≤ ModelWithLimitedPreemptions.task_last_nps task_preemption_points tsk := by
               show ε ≤ last0 (distances (task_preemption_points tsk))
               rw [last0_nth]
               exact h_nonempty tsk ((distances (task_preemption_points tsk)).length - 1) H_tsk_in_ts (by omega)
             simp only [ModelWithLimitedPreemptions.job_last_nps,
               ModelWithLimitedPreemptions.task_last_nps,
               ModelWithLimitedPreemptions.lengths_of_segments, Time, ε] at *
             omega⟩
        higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive
        (blocking_bound_fixed ts tsk higher_eq_priority task_preemption_points)
        H_priority_inversion_is_bounded
        L H_L_positive H_fixed_point_fixed R
        (fun A hA => by
          obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum_fixed A hA
          have h_nd_tsk := H_model_with_fixed_preemption_points.2.2.2.1 tsk H_tsk_in_ts
          have h_end_tsk := H_model_with_fixed_preemption_points.2.2.1 tsk H_tsk_in_ts
          have h_tlns_le : ModelWithLimitedPreemptions.task_last_nps task_preemption_points tsk ≤ task_cost tsk :=
            le_trans (last_of_seq_le_max_of_seq _)
              (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_tsk) (le_of_eq h_end_tsk))
          exact ⟨F, by simp only [Time, ε] at *; omega, by simp only [Time, ε] at *; omega⟩)

  end RTAforFixedPreemptionPointsModelwithArrivalCurves

  section RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves

    variable (job_preemption_points : Job → List Time)
    variable (task_max_nps_float : Task → Time)
    variable (H_task_model_with_floating_nonpreemptive_regions :
      ModelWithLimitedPreemptions.model_with_floating_nonpreemptive_regions
        job_cost job_task arr_seq job_preemption_points task_max_nps_float)

    variable (H_schedule_with_limited_preemptions :
      ModelWithLimitedPreemptions.is_schedule_with_limited_preemptions
        arr_seq job_preemption_points sched)

    variable (H_respects_policy_floating :
      respects_FP_policy_at_preemption_point
        job_arrival job_cost job_task arr_seq sched
        (ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
          job_preemption_points) higher_eq_priority)

    private noncomputable def blocking_bound_floating : Nat :=
      ((ts.filter (fun tsk_other => !higher_eq_priority tsk_other tsk)).map
        (fun tsk_other => task_max_nps_float tsk_other - ε)).foldl max 0

    variable (L : Time)
    variable (H_L_positive : L > 0)
    variable (H_fixed_point_floating :
      L = blocking_bound_floating ts tsk higher_eq_priority task_max_nps_float +
          total_hep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk L)

    variable (R : Nat)
    variable (H_R_is_maximum_floating :
      ∀ A,
        A < L ∧ task_request_bound_function task_cost max_arrivals tsk A ≠
          task_request_bound_function task_cost max_arrivals tsk (A + ε) →
        ∃ F,
          A + F = blocking_bound_floating ts tsk higher_eq_priority task_max_nps_float
                  + task_request_bound_function task_cost max_arrivals tsk (A + ε)
                  + total_ohep_request_bound_function_FP task_cost higher_eq_priority max_arrivals ts tsk (A + F) ∧
          F ≤ R)

    variable (H_priority_inversion_is_bounded :
      priority_inversion_is_bounded_by job_arrival job_cost job_task arr_seq sched
        (FP_to_JLFP job_task higher_eq_priority) tsk
        (blocking_bound_floating ts tsk higher_eq_priority task_max_nps_float))

    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset
      H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_work_conserving H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive
      H_task_model_with_floating_nonpreemptive_regions H_schedule_with_limited_preemptions
      H_respects_policy_floating H_L_positive H_fixed_point_floating H_R_is_maximum_floating H_priority_inversion_is_bounded in
    include H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset H_job_cost_le_task_cost H_family_of_proper_arrival_curves H_tsk_in_ts H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_sequential_jobs H_priority_is_reflexive H_priority_is_transitive H_task_model_with_floating_nonpreemptive_regions H_schedule_with_limited_preemptions H_respects_policy_floating H_L_positive H_fixed_point_floating H_R_is_maximum_floating H_priority_inversion_is_bounded in
    theorem uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions :
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk R := by
      apply Prosa.Classic.Model.Schedule.Uni.Limited.Fixed_priority.Response_time_bound.AbstractRTAforFPwithArrivalCurves.uniprocessor_response_time_bound_fp
        task_cost job_arrival job_cost job_task arr_seq
        H_arrival_times_are_consistent H_arr_seq_is_a_set sched
        H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
        H_work_conserving H_sequential_jobs H_job_cost_le_task_cost ts H_all_jobs_from_taskset
        max_arrivals H_family_of_proper_arrival_curves tsk H_tsk_in_ts
        (fun j => job_cost j - (ModelWithLimitedPreemptions.job_last_nps job_preemption_points j - ε))
        (fun _t => task_cost _t)
        -- proper_job_lock_in_service
        ⟨fun j hARR hPOS => by
           have hLAST := H_task_model_with_floating_nonpreemptive_regions.1.2.1 j hARR hPOS
           have h_nd_j := H_task_model_with_floating_nonpreemptive_regions.1.2.2.2.2 j hARR
           have h_end_j := H_task_model_with_floating_nonpreemptive_regions.1.2.2.2.1 j hARR
           have h_jlns_le : ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
             le_trans (last_of_seq_le_max_of_seq _)
               (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd_j) (le_of_eq h_end_j))
           simp only [Time, ε] at *; omega,
         fun j _hARR _hPOS => Nat.sub_le _ _,
         fun j t t' hARR hLE hSERV hNCOMPL => by
           have h_nd := H_task_model_with_floating_nonpreemptive_regions.1.2.2.2.2 j hARR
           have h_end := H_task_model_with_floating_nonpreemptive_regions.1.2.2.2.1 j hARR
           have h_beg := H_task_model_with_floating_nonpreemptive_regions.1.2.2.1 j hARR
           have hS_lt : service sched j t' < job_cost j := not_le.mp hNCOMPL
           have hS_ge : job_cost j -
               (ModelWithLimitedPreemptions.job_last_nps job_preemption_points j - ε) ≤
               service sched j t' := le_trans hSERV (service_monotonic sched j t t' hLE)
           have hPOS : job_cost j > 0 := Nat.lt_of_le_of_lt (Nat.zero_le _) hS_lt
           have hLAST_pos := H_task_model_with_floating_nonpreemptive_regions.1.2.1 j hARR hPOS
           have h_jlns_le : ModelWithLimitedPreemptions.job_last_nps job_preemption_points j ≤ job_cost j :=
             le_trans (last_of_seq_le_max_of_seq _)
               (le_trans (max_distance_in_seq_le_last_element_of_seq _ h_nd) (le_of_eq h_end))
           have h_len : 2 ≤ (job_preemption_points j).length := by
             by_contra hlt; push_neg at hlt
             have hle1 : (job_preemption_points j).length ≤ 1 := by omega
             have hfe : first0 (job_preemption_points j) = last0 (job_preemption_points j) := by
               cases hq : (job_preemption_points j) with
               | nil => simp [first0, last0, List.headD, List.getLastD]
               | cons a tl =>
                 cases tl with
                 | nil => simp [first0, last0, List.headD, List.getLastD]
                 | cons b rest => simp [hq] at hle1
             rw [h_beg, h_end] at hfe; omega
           have h_lsmd := last_seq_minus_last_distance_seq (job_preemption_points j) h_nd
           rw [h_end] at h_lsmd
           have h_last := last0_nth (job_preemption_points j)
           rw [h_end] at h_last
           have h_len_eq : (job_preemption_points j).length - 2 + 1 =
               (job_preemption_points j).length - 1 := by omega
           have h_jlns_eq : ModelWithLimitedPreemptions.job_last_nps job_preemption_points j =
               last0 (distances (job_preemption_points j)) := rfl
           have h_gt : nthD (job_preemption_points j)
               ((job_preemption_points j).length - 2) < service sched j t' := by
             simp only [h_jlns_eq, Time, ε] at hS_ge hLAST_pos h_jlns_le h_lsmd ⊢; omega
           have h_lt : service sched j t' < nthD (job_preemption_points j)
               ((job_preemption_points j).length - 2 + 1) := by
             rw [h_len_eq, ← h_last]; exact hS_lt
           have h_not_mem := antidensity_of_nondecreasing_seq _ _ _ h_nd ⟨h_gt, h_lt⟩
           have h_cant : ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
               job_preemption_points j (service sched j t') = false := by
             unfold ModelWithLimitedPreemptions.can_be_preempted_for_model_with_limited_preemptions
             exact decide_eq_false h_not_mem
           exact H_schedule_with_limited_preemptions j t' hARR h_cant⟩
        -- proper_task_lock_in_service
        ⟨le_refl _,
         fun j hARR hTSK => by
           have hCOST : job_cost j ≤ task_cost (job_task j) := H_job_cost_le_task_cost j hARR
           rw [hTSK] at hCOST
           exact le_trans (Nat.sub_le _ _) hCOST⟩
        higher_eq_priority H_priority_is_reflexive
        H_priority_is_transitive
        (blocking_bound_floating ts tsk higher_eq_priority task_max_nps_float)
        H_priority_inversion_is_bounded
        L H_L_positive H_fixed_point_floating R
        (fun A hA => by
          obtain ⟨F, hFIX, hLE⟩ := H_R_is_maximum_floating A hA
          exact ⟨F, by simp only [Time] at *; omega, by simp only [Nat.sub_self, Nat.add_zero]; exact hLE⟩)

  end RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves

end Analysis

end RTAforConcreteModels

end Prosa.Classic.Model.Schedule.Uni.Limited.Fixed_priority.Nonpr_reg.Concrete_models.Response_time_bound
