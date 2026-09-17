-- Translated from: ../rt-proofs/classic/analysis/uni/susp/dynamic/jitter/jitter_schedule_service.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule_properties
import Prosa.Classic.Model.Schedule.Uni.Transformation.Construction
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Schedule.Uni.Response_time
noncomputable section
namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule_service
open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Workload
open Prosa.Classic.Model.Schedule.Uni.Service
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule.JitterScheduleConstruction
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule_properties.JitterScheduleProperties
def valid_suspension_aware_schedule {Task : Type _} [DecidableEq Task] {Job : Type _} [DecidableEq Job] (job_arrival : Job → Time) (arr_seq : arrival_sequence Job) (higher_eq_priority : JLDP_policy Job) (job_suspension_duration : job_suspension Job) (job_cost : Job → Time) (sched_susp : schedule Job) : Prop :=
  jobs_come_from_arrival_sequence sched_susp arr_seq ∧ jobs_must_arrive_to_execute job_arrival sched_susp ∧ completed_jobs_dont_execute job_cost sched_susp ∧
  (∀ j t, arrives_in arr_seq j → (pending job_arrival job_cost sched_susp j t ∧ ¬ (scheduled_at sched_susp j t = true) ∧ ¬ suspended_at job_arrival job_cost job_suspension_duration sched_susp j t) → ∃ j_other, scheduled_at sched_susp j_other t = true) ∧
  (∀ j j_hp t, arrives_in arr_seq j → (pending job_arrival job_cost sched_susp j t ∧ ¬ (scheduled_at sched_susp j t = true) ∧ ¬ suspended_at job_arrival job_cost job_suspension_duration sched_susp j t) → scheduled_at sched_susp j_hp t = true → higher_eq_priority t j_hp j = true) ∧
  respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp
section ProvingScheduleProperties
variable {Task : Type _} [DecidableEq Task]
variable (task_cost task_period task_deadline : Task → Time)
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival job_cost job_deadline : Job → Time) (job_task : Job → Task)
variable (ts : List Task) (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
variable (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
variable (H_job_deadlines_equal_task_deadlines : ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
variable (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
variable (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
variable (higher_eq_priority : FP_policy Task)
variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
variable (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)
variable (job_suspension_duration : job_suspension Job) (sched_susp : schedule Job)
variable (H_valid_schedule : @valid_suspension_aware_schedule Task _ Job _ job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched_susp)
variable (j : Job) (H_from_arrival_sequence : arrives_in arr_seq j) (R_j : Time) (R_hp : Job → Time)
variable (H_bounded_response_time_of_hp_jobs : ∀ j_hp, arrives_in arr_seq j_hp → (higher_eq_priority (job_task j_hp) (job_task j) && decide (job_task j_hp ≠ job_task j)) = true → is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (R_hp j_hp))
variable (H_no_deadline_misses_for_previous_jobs : ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j → Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
def workload_of_other_hep_jobs_in_sched_susp (t1 t2 : Time) : Nat :=
  workload_of_jobs job_cost (jobs_arrived_between arr_seq t1 t2) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j))
def workload_of_other_hep_jobs_in_sched_jitter (t1 t2 : Time) : Nat :=
  workload_of_jobs (inflated_job_cost job_cost job_suspension_duration j) (actual_arrivals_between job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq t1 t2) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j))
def service_of_other_hep_jobs_in_sched_susp (t1 t2 : Time) : Nat :=
  service_of_jobs sched_susp (jobs_arrived_between arr_seq 0 (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j)) t1 t2
def service_of_other_hep_jobs_in_sched_jitter (t1 t2 : Time) : Nat :=
  service_of_jobs (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) (actual_arrivals_between job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq 0 (job_arrival j + R_j)) (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j)) t1 t2
section AuxiliaryLemmas
section ServiceEqualsWorkload
variable (t : Time) (H_before_end_of_interval : t ≤ job_arrival j + R_j)
variable (H_workload_has_finished : ∀ j_hp, arrives_in arr_seq j_hp → actual_arrival_before job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp t → (higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j)) = true → completed_by (inflated_job_cost job_cost job_suspension_duration j) (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j_hp t)
include H_workload_has_finished H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    H_before_end_of_interval in
theorem jitter_reduction_service_equals_workload_in_jitter : service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp 0 t ≥ workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp 0 t := by
  show workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq
    higher_eq_priority job_suspension_duration j R_hp 0 t ≤
    service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq
    higher_eq_priority job_suspension_duration j R_j R_hp 0 t
  unfold service_of_other_hep_jobs_in_sched_jitter workload_of_other_hep_jobs_in_sched_jitter
    service_of_jobs workload_of_jobs
  apply le_trans
  · -- Step 1: workload(act 0 t) ≤ service(act 0 t, [0,t))
    apply Prosa.Util.Sum.leq_sum_seq
    intro j_hp hmem hhep
    -- completed_by gives inflated_cost ≤ service 0 t = service_during 0 t
    exact H_workload_has_finished j_hp
      (in_actual_arrivals_between_implies_arrived job_arrival
        (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq
        H_arrival_times_are_consistent j_hp 0 t hmem)
      (in_actual_arrivals_implies_arrived_before job_arrival
        (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq
        H_arrival_times_are_consistent j_hp t hmem)
      hhep
  · -- Step 2: service(act 0 t) ≤ service(act 0 (arr_j+R_j))  [subset + nodup]
    apply Prosa.Classic.Util.Sum.leq_sum_sub_uniq
    · exact List.Nodup.filter _
        (actual_arrivals_uniq job_arrival
          (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq
          H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0 t)
    · intro x hmem
      simp only [List.mem_filter] at hmem ⊢
      exact ⟨actual_arrivals_between_sub job_arrival
        (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq
        H_arrival_times_are_consistent x 0 0 t (job_arrival j + R_j)
        le_rfl H_before_end_of_interval hmem.1, hmem.2⟩
end ServiceEqualsWorkload
section ServiceBoundedByWorkload
variable (t : Time) (H_before_end_of_interval : t ≤ job_arrival j + R_j)
include H_valid_schedule H_arrival_times_are_consistent H_before_end_of_interval in
theorem jitter_reduction_service_in_sched_susp_le_workload : service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j 0 t ≤ workload_of_other_hep_jobs_in_sched_susp job_cost job_task arr_seq higher_eq_priority j 0 t := by
  have ⟨FROMarr, MUSTARRs, COMPs, _⟩ := H_valid_schedule
  unfold service_of_other_hep_jobs_in_sched_susp workload_of_other_hep_jobs_in_sched_susp
    service_of_jobs workload_of_jobs
  -- Split job list: arr(0,arr_j+R_j) = arr(0,t) ++ arr(t, arr_j+R_j)
  rw [job_arrived_between_cat arr_seq 0 t (job_arrival j + R_j)
    (Nat.zero_le t) H_before_end_of_interval]
  simp only [List.filter_append, List.map_append, List.sum_append]
  -- The extra jobs (arriving in [t, arr_j+R_j)) have zero service during [0,t)
  have h_zero : ∀ j0, j0 ∈ jobs_arrived_between arr_seq t (job_arrival j + R_j) →
      service_during sched_susp j0 0 t = 0 := by
    intro j0 h_in
    simp only [service_during]
    apply Finset.sum_eq_zero
    intro t' ht'
    rw [Finset.mem_Ico] at ht'
    simp only [service_at]
    have h_arrived := in_arrivals_implies_arrived_between job_arrival arr_seq
      H_arrival_times_are_consistent j0 t (job_arrival j + R_j) h_in
    by_cases h_sched : scheduled_at sched_susp j0 t' = true
    · have h_arr := MUSTARRs j0 t' h_sched
      simp only [has_arrived] at h_arr
      exact absurd (le_trans h_arrived.1 h_arr) (not_le.mpr ht'.2)
    · have h_false : scheduled_at sched_susp j0 t' = false := by
        cases h : scheduled_at sched_susp j0 t' <;> simp_all
      simp [service_at, h_false]
  have h_extra_sum :
      (List.map (fun j_1 => service_during sched_susp j_1 0 t)
        (List.filter (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) &&
          decide (j_hp ≠ j)) (jobs_arrived_between arr_seq t (job_arrival j + R_j)))).sum = 0 := by
    apply List.sum_eq_zero
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨j0, hj0_mem, rfl⟩ := hx
    rw [List.mem_filter] at hj0_mem
    exact h_zero j0 hj0_mem.1
  rw [h_extra_sum, Nat.add_zero]
  -- Now: ∑(arr(0,t).filter hep) sd(·,0,t) ≤ ∑(arr(0,t).filter hep) cost
  exact Prosa.Util.Sum.leq_sum_seq _ _ _ _ (fun j0 _ _ =>
    cumulative_service_le_job_cost job_cost sched_susp j0 COMPs 0 t)
end ServiceBoundedByWorkload
end AuxiliaryLemmas
section LessServiceBeforeArrival
section LessServiceForEachJob
variable (j_hp : Job) (H_arrives : arrives_in arr_seq j_hp)
variable (H_higher_or_equal_priority : (higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j)) = true)
section Case1
variable (H_same_task : job_task j_hp = job_task j)
include H_same_task H_arrives H_higher_or_equal_priority H_valid_schedule
    H_no_deadline_misses_for_previous_jobs H_job_deadlines_equal_task_deadlines
    H_constrained_deadlines H_sporadic_arrivals H_jobs_from_taskset H_from_arrival_sequence in
theorem jitter_reduction_less_job_service_before_interval_case1 : service (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  have h_ne : j_hp ≠ j := by
    have h := H_higher_or_equal_priority; simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  by_cases hBefore : job_arrival j_hp < job_arrival j
  · -- j_hp arrives before j: use deadline miss + sporadic + constrained
    have h_comp : completed_jobs_dont_execute
        (inflated_job_cost job_cost job_suspension_duration j)
        (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) :=
      sched_jitter_completed_jobs_dont_execute job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R_hp
    have h1 := cumulative_service_le_job_cost
      (inflated_job_cost job_cost job_suspension_duration j)
      (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp)
      j_hp h_comp 0 (job_arrival j)
    have h_inf : inflated_job_cost job_cost job_suspension_duration j j_hp = job_cost j_hp := by
      simp only [inflated_job_cost, beq_iff_eq, h_ne, ↓reduceIte]
    have h_nomiss := H_no_deadline_misses_for_previous_jobs j_hp H_arrives hBefore H_same_task
    have h_dl := H_job_deadlines_equal_task_deadlines j_hp H_arrives
    have h_in_ts := H_jobs_from_taskset j_hp H_arrives
    have h_cdl := H_constrained_deadlines (job_task j_hp) h_in_ts
    have h_spo := H_sporadic_arrivals j_hp j h_ne H_arrives H_from_arrival_sequence
      H_same_task (Nat.le_of_lt hBefore)
    have h_deadline_le : job_arrival j_hp + job_deadline j_hp ≤ job_arrival j :=
      calc job_arrival j_hp + job_deadline j_hp
          = job_arrival j_hp + task_deadline (job_task j_hp) := by rw [h_dl]
        _ ≤ job_arrival j_hp + task_period (job_task j_hp) := Nat.add_le_add_left h_cdl _
        _ ≤ job_arrival j := h_spo
    apply le_trans h1; rw [h_inf]
    -- Bridge Schedulability.service to Schedule.service
    have h_sa_eq : ∀ t', Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at sched_susp
        j_hp t' = service_at sched_susp j_hp t' := by
      intro t'
      simp only [Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at,
        Prosa.Classic.Model.Schedule.Uni.Schedulability.scheduled_at,
        service_at, scheduled_at]
      have : ∀ (b : Bool), (if b = true then 1 else 0) = b.toNat := by intro b; cases b <;> rfl
      exact this _
    have h_mono := Prosa.Classic.Model.Schedule.Uni.Schedulability.completion_monotonic
      job_cost sched_susp j_hp _ (job_arrival j) h_deadline_le h_nomiss
    simp only [Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_by,
      Prosa.Classic.Model.Schedule.Uni.Schedulability.service,
      Prosa.Classic.Model.Schedule.Uni.Schedulability.service_during,
      h_sa_eq, service, service_during] at h_mono
    exact h_mono
  · -- j_hp arrives at or after j: same task → jitter = 0, so service = 0
    push_neg at hBefore
    show service_during _ j_hp 0 (job_arrival j) ≤ _
    simp only [service_during]
    have h_exec : jobs_execute_after_jitter job_arrival
        (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp)
        (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) :=
      sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority
        job_cost job_suspension_duration j R_hp
    have h_arr : job_arrival j ≤ actual_arrival job_arrival
        (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp := by
      unfold actual_arrival job_jitter
      have hcond : (higher_eq_priority (job_task j_hp) (job_task j) &&
          decide (job_task j_hp ≠ job_task j)) = false := by
        simp only [H_same_task, ne_eq, not_true_eq_false, decide_false, Bool.and_false]
      simp only [hcond, ↓reduceIte, Nat.add_zero]
      exact hBefore
    have h_zero := cumulative_service_before_jitter_is_zero job_arrival
      (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp)
      (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp)
      h_exec j_hp 0 (job_arrival j) h_arr
    rw [h_zero]
    exact Nat.zero_le _
end Case1
section Case2
variable (H_different_task : job_task j_hp ≠ job_task j) (H_released_no_earlier : job_arrival j ≤ actual_arrival job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp)
include H_released_no_earlier in
theorem jitter_reduction_less_job_service_before_interval_case2 : service (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  show service_during _ j_hp 0 (job_arrival j) ≤ _
  simp only [service_during]
  have h_exec : jobs_execute_after_jitter job_arrival
      (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp)
      (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) :=
    sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority
      job_cost job_suspension_duration j R_hp
  have h_zero := cumulative_service_before_jitter_is_zero job_arrival
    (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp)
    (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp)
    h_exec j_hp 0 (job_arrival j) H_released_no_earlier
  rw [h_zero]
  exact Nat.zero_le _
end Case2
section Case3
variable (H_different_task : job_task j_hp ≠ job_task j) (H_distance_is_smaller : job_arrival j - job_arrival j_hp < R_hp j_hp - job_cost j_hp)
include H_higher_or_equal_priority H_different_task H_distance_is_smaller in
theorem jitter_reduction_less_job_service_before_interval_case3 : service (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  show service_during _ j_hp 0 (job_arrival j) ≤ _
  simp only [service_during]
  have h_exec : jobs_execute_after_jitter job_arrival
      (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp)
      (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) :=
    sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority
      job_cost job_suspension_duration j R_hp
  have h_arr : job_arrival j ≤ actual_arrival job_arrival
      (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp := by
    unfold actual_arrival job_jitter
    have hhep : higher_eq_priority (job_task j_hp) (job_task j) = true := by
      have h := H_higher_or_equal_priority
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
    have hcond : (higher_eq_priority (job_task j_hp) (job_task j) &&
        decide (job_task j_hp ≠ job_task j)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hhep, H_different_task⟩
    rw [if_pos hcond, min_eq_left (Nat.le_of_lt H_distance_is_smaller)]
    exact le_add_tsub
  have h_zero := cumulative_service_before_jitter_is_zero job_arrival
    (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp)
    (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp)
    h_exec j_hp 0 (job_arrival j) h_arr
  rw [h_zero]
  exact Nat.zero_le _
end Case3
section Case4
variable (H_different_task : job_task j_hp ≠ job_task j) (H_completes_before_j_arrives : job_arrival j_hp + R_hp j_hp ≤ job_arrival j)
include H_arrives H_higher_or_equal_priority H_different_task H_completes_before_j_arrives H_bounded_response_time_of_hp_jobs in
theorem jitter_reduction_less_job_service_before_interval_case4 : service (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  have h_ne : j_hp ≠ j := by
    have h := H_higher_or_equal_priority; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  have hhep : higher_eq_priority (job_task j_hp) (job_task j) = true := by
    have h := H_higher_or_equal_priority; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  have h_comp : completed_jobs_dont_execute
      (inflated_job_cost job_cost job_suspension_duration j)
      (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) :=
    sched_jitter_completed_jobs_dont_execute job_arrival job_task arr_seq higher_eq_priority
      job_cost job_suspension_duration j R_hp
  have h1 := cumulative_service_le_job_cost
    (inflated_job_cost job_cost job_suspension_duration j)
    (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp)
    j_hp h_comp 0 (job_arrival j)
  have h_inf : inflated_job_cost job_cost job_suspension_duration j j_hp = job_cost j_hp := by
    simp only [inflated_job_cost, beq_iff_eq, h_ne, ↓reduceIte]
  have h_task_cond : (higher_eq_priority (job_task j_hp) (job_task j) &&
      decide (job_task j_hp ≠ job_task j)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hhep, H_different_task⟩
  have h_resp : job_cost j_hp ≤ service sched_susp j_hp (job_arrival j_hp + R_hp j_hp) :=
    H_bounded_response_time_of_hp_jobs j_hp H_arrives h_task_cond
  apply le_trans h1
  rw [h_inf]
  apply le_trans h_resp
  simp only [service, service_during]
  exact Prosa.Classic.Util.Sum.extend_sum 0 (job_arrival j_hp + R_hp j_hp) 0 (job_arrival j) _ le_rfl H_completes_before_j_arrives
end Case4
section Case5
variable (H_different_task : job_task j_hp ≠ job_task j) (H_released_before : actual_arrival job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp < job_arrival j) (H_j_hp_completes_after_j_arrives : job_arrival j < job_arrival j_hp + R_hp j_hp) (H_distance_is_not_smaller : R_hp j_hp - job_cost j_hp ≤ job_arrival j - job_arrival j_hp)
include H_higher_or_equal_priority H_different_task H_distance_is_not_smaller in
theorem jitter_reduction_jitter_equals_R_minus_cost : job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp j_hp = R_hp j_hp - job_cost j_hp := by
  unfold job_jitter
  have hcond : (higher_eq_priority (job_task j_hp) (job_task j) && decide (job_task j_hp ≠ job_task j)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨by have h := H_higher_or_equal_priority; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1, H_different_task⟩
  simp only [hcond, ↓reduceIte]
  exact min_eq_right H_distance_is_not_smaller
include H_arrives H_higher_or_equal_priority H_different_task H_released_before
    H_j_hp_completes_after_j_arrives H_distance_is_not_smaller H_bounded_response_time_of_hp_jobs in
theorem jitter_reduction_less_job_service_before_interval_case5 : service (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  have h_ne : j_hp ≠ j := by
    have h := H_higher_or_equal_priority; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  have hhep : higher_eq_priority (job_task j_hp) (job_task j) = true := by
    have h := H_higher_or_equal_priority; simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1
  have h_task_cond : (higher_eq_priority (job_task j_hp) (job_task j) &&
      decide (job_task j_hp ≠ job_task j)) = true := by
    simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hhep, H_different_task⟩
  have h_exec : jobs_execute_after_jitter job_arrival
      (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp)
      (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) :=
    sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority
      job_cost job_suspension_duration j R_hp
  have h_jit := jitter_reduction_jitter_equals_R_minus_cost job_arrival job_cost job_task
    higher_eq_priority j R_hp j_hp H_higher_or_equal_priority
    H_different_task H_distance_is_not_smaller
  -- Part 1: Split service at actual_arrival, bound by interval length
  show service_during _ j_hp 0 (job_arrival j) ≤ _
  simp only [service_during]
  rw [ignore_service_before_jitter job_arrival
    (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp)
    (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp)
    h_exec j_hp 0 (job_arrival j) (Nat.zero_le _) (Nat.le_of_lt H_released_before)]
  -- Goal: ∑_{actual_arrival..arr_j} service_at sched_jitter j_hp ≤ service sched_susp j_hp arr_j
  apply le_trans (Finset.sum_le_card_nsmul _ _ 1 (fun t _ => by
    simp only [service_at]; exact Bool.toNat_le _))
  simp
  -- Goal: arr_j ≤ service sched_susp j_hp arr_j + actual_arrival j_hp
  -- Part 2: Lower bound on service_susp via response time bound
  simp only [service, service_during]
  -- Bridge Schedulability.service in h_resp to Finset.Ico sum
  have h_sa_eq : ∀ t', Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at sched_susp
      j_hp t' = service_at sched_susp j_hp t' := by
    intro t'
    simp only [Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at,
      Prosa.Classic.Model.Schedule.Uni.Schedulability.scheduled_at, service_at, scheduled_at]
    have : ∀ (b : Bool), (if b = true then 1 else 0) = b.toNat := by intro b; cases b <;> rfl
    exact this _
  have h_resp' : job_cost j_hp ≤ ∑ t' ∈ Finset.Ico 0 (job_arrival j_hp + R_hp j_hp),
      service_at sched_susp j_hp t' := by
    have h := H_bounded_response_time_of_hp_jobs j_hp H_arrives h_task_cond
    simp only [Prosa.Classic.Model.Schedule.Uni.Schedulability.is_response_time_bound_of_job,
      Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_by,
      Prosa.Classic.Model.Schedule.Uni.Schedulability.service,
      Prosa.Classic.Model.Schedule.Uni.Schedulability.service_during, h_sa_eq] at h
    exact h
  -- Bound the tail: ∑_{arr_j..arr_hp+Rhp} ≤ arr_hp+Rhp - arr_j
  have h_tail : ∑ t' ∈ Finset.Ico (job_arrival j) (job_arrival j_hp + R_hp j_hp),
      service_at sched_susp j_hp t' ≤ job_arrival j_hp + R_hp j_hp - job_arrival j := by
    apply le_trans (Finset.sum_le_card_nsmul _ _ 1 (fun t _ => by
      simp only [service_at]; exact Bool.toNat_le _))
    simp
  -- actual_arrival = arr_hp + jitter = arr_hp + (Rhp - cost_hp)
  have h_aa : actual_arrival job_arrival (job_jitter job_arrival job_task higher_eq_priority
      job_cost j R_hp) j_hp = job_arrival j_hp + (R_hp j_hp - job_cost j_hp) := by
    unfold actual_arrival; rw [h_jit]
  rw [h_aa]
  -- Derive the key bound: cost ≤ ∑_{0..arr_j} service + ∑_{arr_j..arr_hp+R} service
  have h_key : job_cost j_hp ≤
      Finset.sum (Finset.Ico 0 (job_arrival j)) (fun t' => service_at sched_susp j_hp t') +
      Finset.sum (Finset.Ico (job_arrival j) (job_arrival j_hp + R_hp j_hp))
        (fun t' => service_at sched_susp j_hp t') := by
    calc job_cost j_hp
        ≤ ∑ t' ∈ Finset.Ico 0 (job_arrival j_hp + R_hp j_hp),
            service_at sched_susp j_hp t' := h_resp'
      _ = _ := (Finset.sum_Ico_consecutive _ (Nat.zero_le _)
                 (Nat.le_of_lt H_j_hp_completes_after_j_arrives)).symm
  -- Combine h_key and h_tail to eliminate the tail sum
  have h_bound : job_cost j_hp ≤
      Finset.sum (Finset.Ico 0 (job_arrival j)) (fun t' => service_at sched_susp j_hp t') +
      (job_arrival j_hp + R_hp j_hp - job_arrival j) :=
    le_trans h_key (Nat.add_le_add_left h_tail _)
  -- Derive: cost + arr_j ≤ ∑ service + (arr_hp + R) [avoids Nat sub]
  have h_add : job_cost j_hp + job_arrival j ≤
      Finset.sum (Finset.Ico 0 (job_arrival j)) (fun t' => service_at sched_susp j_hp t') +
      (job_arrival j_hp + R_hp j_hp) := by
    have h1 := Nat.add_le_add_right h_bound (job_arrival j)
    rw [Nat.add_assoc,
      Nat.sub_add_cancel (Nat.le_of_lt H_j_hp_completes_after_j_arrives)] at h1
    exact h1
  clear h_key h_bound h_resp' h_tail h_sa_eq h_exec h_jit h_task_cond hhep h_ne h_aa
  clear H_arrives H_bounded_response_time_of_hp_jobs H_released_before
  zify [H_j_hp_completes_after_j_arrives.le, H_distance_is_not_smaller] at h_add ⊢
  omega
end Case5
include H_arrives H_higher_or_equal_priority H_valid_schedule
    H_no_deadline_misses_for_previous_jobs H_job_deadlines_equal_task_deadlines
    H_constrained_deadlines H_sporadic_arrivals H_jobs_from_taskset H_from_arrival_sequence
    H_bounded_response_time_of_hp_jobs in
theorem jitter_reduction_less_job_service_before_interval : service (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j_hp (job_arrival j) ≤ service sched_susp j_hp (job_arrival j) := by
  by_cases hSame : job_task j_hp = job_task j
  · exact jitter_reduction_less_job_service_before_interval_case1
      task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq
      H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines
      H_sporadic_arrivals higher_eq_priority job_suspension_duration sched_susp H_valid_schedule
      j H_from_arrival_sequence R_hp H_no_deadline_misses_for_previous_jobs j_hp H_arrives
      H_higher_or_equal_priority hSame
  · by_cases hReleased : job_arrival j ≤ actual_arrival job_arrival
        (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp
    · exact jitter_reduction_less_job_service_before_interval_case2
        job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration
        sched_susp j R_hp j_hp hReleased
    · push_neg at hReleased
      by_cases hDist : job_arrival j - job_arrival j_hp < R_hp j_hp - job_cost j_hp
      · exact jitter_reduction_less_job_service_before_interval_case3
          job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration
          sched_susp j R_hp j_hp H_higher_or_equal_priority hSame hDist
      · push_neg at hDist
        by_cases hCompl : job_arrival j_hp + R_hp j_hp ≤ job_arrival j
        · exact jitter_reduction_less_job_service_before_interval_case4
            job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration
            sched_susp j R_hp H_bounded_response_time_of_hp_jobs j_hp H_arrives
            H_higher_or_equal_priority hSame hCompl
        · push_neg at hCompl
          exact jitter_reduction_less_job_service_before_interval_case5
            job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration
            sched_susp j R_hp H_bounded_response_time_of_hp_jobs j_hp H_arrives
            H_higher_or_equal_priority hSame hReleased hCompl hDist
end LessServiceForEachJob
include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
    H_valid_schedule H_from_arrival_sequence H_bounded_response_time_of_hp_jobs
    H_no_deadline_misses_for_previous_jobs in
theorem jitter_reduction_less_service_before_the_interval : service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp 0 (job_arrival j) ≤ service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j 0 (job_arrival j) := by
  unfold service_of_other_hep_jobs_in_sched_jitter service_of_other_hep_jobs_in_sched_susp
    service_of_jobs
  -- Step 1: per-job bound over actual_arrivals
  apply le_trans
  · apply Prosa.Util.Sum.leq_sum_seq
    intro j_hp hmem hhep
    -- service_during = service for 0-start, both definitionally equal
    exact jitter_reduction_less_job_service_before_interval
      task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq
      H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines
      H_sporadic_arrivals higher_eq_priority job_suspension_duration sched_susp H_valid_schedule
      j H_from_arrival_sequence R_hp H_bounded_response_time_of_hp_jobs
      H_no_deadline_misses_for_previous_jobs j_hp
      (in_actual_arrivals_between_implies_arrived job_arrival
        (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq
        H_arrival_times_are_consistent j_hp 0 (job_arrival j + R_j) hmem) hhep
  · -- Step 2: actual_arrivals.filter hep ⊆ arrivals.filter hep
    apply Prosa.Classic.Util.Sum.leq_sum_sub_uniq
    · apply List.Nodup.filter
      exact actual_arrivals_uniq job_arrival
        (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq
        H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0 (job_arrival j + R_j)
    · intro x hmem
      simp only [List.mem_filter] at hmem ⊢
      refine ⟨?_, hmem.2⟩
      -- x ∈ actual_arrivals_between ⊆ jobs_arrived_before = jobs_arrived_between
      have h := hmem.1
      simp only [actual_arrivals_between] at h
      exact List.mem_of_mem_filter h
end LessServiceBeforeArrival
section MoreServiceAfterArrival
section Conservation
variable (t : Time) (H_no_earlier_than_j : t ≥ job_arrival j)
include H_no_earlier_than_j in
theorem jitter_reduction_actual_arrival_before_end_of_interval : ∀ j_hp, (higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j)) = true → job_arrival j_hp ≤ t → actual_arrival job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp ≤ t := by
  intro j_hp hep harr
  unfold actual_arrival job_jitter
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hep
  by_cases hdiff : job_task j_hp ≠ job_task j
  · have hcond : (higher_eq_priority (job_task j_hp) (job_task j) && decide (job_task j_hp ≠ job_task j)) = true := by
      simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hep.1, hdiff⟩
    simp only [hcond, ↓reduceIte]
    calc job_arrival j_hp + min (job_arrival j - job_arrival j_hp) (R_hp j_hp - job_cost j_hp)
        ≤ job_arrival j_hp + (job_arrival j - job_arrival j_hp) := by
          apply Nat.add_le_add_left; exact Nat.min_le_left _ _
      _ ≤ t := by
          by_cases h : job_arrival j_hp ≤ job_arrival j
          · rw [Nat.add_sub_cancel' h]; exact H_no_earlier_than_j
          · push_neg at h
            have : job_arrival j - job_arrival j_hp = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_lt h)
            rw [this, Nat.add_zero]; exact harr
  · push_neg at hdiff
    have hcond : (higher_eq_priority (job_task j_hp) (job_task j) && decide (job_task j_hp ≠ job_task j)) = false := by
      simp only [hdiff, ne_eq, not_true_eq_false, decide_false, Bool.and_false]
    simp only [hcond, ↓reduceIte, Nat.add_zero]
    exact harr
include H_no_earlier_than_j H_arrival_times_are_consistent H_arrival_sequence_is_a_set in
theorem jitter_reduction_workload_conservation_inside_interval : workload_of_other_hep_jobs_in_sched_susp job_cost job_task arr_seq higher_eq_priority j 0 (t + 1) ≤ workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp 0 (t + 1) := by
  unfold workload_of_other_hep_jobs_in_sched_susp workload_of_other_hep_jobs_in_sched_jitter
    workload_of_jobs
  apply le_trans
  · -- Step 1: job_cost ≤ inflated_cost for hep jobs (they're ≠ j, so equal)
    apply Prosa.Util.Sum.leq_sum_seq
    intro j0 _ hhep
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hhep
    show job_cost j0 ≤ inflated_job_cost job_cost job_suspension_duration j j0
    unfold inflated_job_cost
    simp [beq_eq_false_iff_ne.mpr hhep.2]
  · -- Step 2: arr(0,t+1).filter(hep) ⊆ act_arr(0,t+1).filter(hep) via subset+nodup
    apply Prosa.Classic.Util.Sum.leq_sum_sub_uniq
    · exact List.Nodup.filter _ (arrivals_uniq job_arrival arr_seq
        H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0 (t + 1))
    · intro x hmem
      simp only [List.mem_filter] at hmem ⊢
      refine ⟨?_, hmem.2⟩
      have h_arrives : arrives_in arr_seq x :=
        in_arrivals_implies_arrived job_arrival arr_seq
          H_arrival_times_are_consistent x 0 (t + 1) hmem.1
      have h_arrived := in_arrivals_implies_arrived_between job_arrival arr_seq
        H_arrival_times_are_consistent x 0 (t + 1) hmem.1
      have h_arr_le : job_arrival x ≤ t := Nat.lt_succ_iff.mp h_arrived.2
      have h_aa_le := jitter_reduction_actual_arrival_before_end_of_interval
        job_arrival job_cost job_task higher_eq_priority j R_hp t H_no_earlier_than_j
        x hmem.2 h_arr_le
      exact arrived_between_implies_in_actual_arrivals job_arrival
        (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) arr_seq
        H_arrival_times_are_consistent x 0 (t + 1) h_arrives
        ⟨Nat.zero_le _, Nat.lt_succ_of_le h_aa_le⟩
end Conservation
section MoreServiceInsideTheInterval
section InductiveStep
variable (d : Time) (H_d_lt_R : d < R_j)
variable (H_induction_hypothesis : service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d))
section NoPendingJobs
variable (H_all_jobs_completed_in_sched_jitter : ∀ j_hp, arrives_in arr_seq j_hp → (higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j)) = true → jitter_has_passed job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp (job_arrival j + d) → completed_by (inflated_job_cost job_cost job_suspension_duration j) (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j_hp (job_arrival j + d))
include H_d_lt_R H_valid_schedule H_arrival_times_are_consistent in
theorem jitter_reduction_convert_service_to_workload : service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d + 1) ≤ workload_of_other_hep_jobs_in_sched_susp job_cost job_task arr_seq higher_eq_priority j 0 (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j 0 (job_arrival j) := by
  apply Prosa.Util.Nat.subh3
  -- s(arr_j, arr_j+d+1) + s(0, arr_j) = s(0, arr_j+d+1) ≤ w(0, arr_j+d+1)
  have h_combine :
      service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority
        sched_susp j R_j (job_arrival j) (job_arrival j + d + 1) +
      service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority
        sched_susp j R_j 0 (job_arrival j) =
      service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority
        sched_susp j R_j 0 (job_arrival j + d + 1) := by
    simp only [service_of_other_hep_jobs_in_sched_susp, service_of_jobs, service_during]
    suffices hkey : ∀ (L : List Job),
        (L.map (fun j0 => ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + d + 1),
          service_at sched_susp j0 t)).sum +
        (L.map (fun j0 => ∑ t ∈ Finset.Ico 0 (job_arrival j),
          service_at sched_susp j0 t)).sum =
        (L.map (fun j0 => ∑ t ∈ Finset.Ico 0 (job_arrival j + d + 1),
          service_at sched_susp j0 t)).sum from hkey _
    intro L; induction L with
    | nil => simp
    | cons a L' ih =>
      simp only [List.map_cons, List.sum_cons]
      have heq : ∑ t ∈ Finset.Ico (job_arrival j) (job_arrival j + d + 1),
          service_at sched_susp a t +
          ∑ t ∈ Finset.Ico 0 (job_arrival j), service_at sched_susp a t =
          ∑ t ∈ Finset.Ico 0 (job_arrival j + d + 1), service_at sched_susp a t := by
        rw [add_comm]
        exact Finset.sum_Ico_consecutive (fun t => service_at sched_susp a t)
          (by omega) (by omega)
      omega
  rw [h_combine]
  exact jitter_reduction_service_in_sched_susp_le_workload job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent higher_eq_priority job_suspension_duration sched_susp
    H_valid_schedule j R_j (job_arrival j + d + 1)
    (Nat.add_le_add_left (Nat.succ_le_of_lt H_d_lt_R) _)
include H_arrival_times_are_consistent H_arrival_sequence_is_a_set in
theorem jitter_reduction_compare_workload : workload_of_other_hep_jobs_in_sched_susp job_cost job_task arr_seq higher_eq_priority j 0 (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j 0 (job_arrival j) ≤ workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp 0 (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j 0 (job_arrival j) := by
  exact Nat.sub_le_sub_right (jitter_reduction_workload_conservation_inside_interval job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration j R_hp (job_arrival j + d) (Nat.le_add_right _ _)) _
include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
    H_valid_schedule H_from_arrival_sequence H_bounded_response_time_of_hp_jobs
    H_no_deadline_misses_for_previous_jobs in
theorem jitter_reduction_compare_service : workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp 0 (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j 0 (job_arrival j) ≤ workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp 0 (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp 0 (job_arrival j) := by
  exact Nat.sub_le_sub_left (jitter_reduction_less_service_before_the_interval task_period task_deadline job_arrival job_cost job_deadline job_task ts arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j R_hp H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs) _
include H_d_lt_R H_all_jobs_completed_in_sched_jitter H_arrival_times_are_consistent
    H_arrival_sequence_is_a_set in
theorem jitter_reduction_convert_workload_to_service : workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_hp 0 (job_arrival j + d + 1) - service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp 0 (job_arrival j) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d + 1) := by
  -- Rearrange: w(0,arr_j+d+1) ≤ s(0,arr_j) + s(arr_j, arr_j+d+1) = s(0, arr_j+d+1)
  suffices h :
      workload_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq
        higher_eq_priority job_suspension_duration j R_hp 0 (job_arrival j + d + 1) ≤
      service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq
        higher_eq_priority job_suspension_duration j R_j R_hp 0 (job_arrival j) +
      service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq
        higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j)
        (job_arrival j + d + 1) by zify [h]; omega
  -- Combine intervals: s(0,arr_j) + s(arr_j,arr_j+d+1) = s(0,arr_j+d+1)
  have h_combine :
      service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq
        higher_eq_priority job_suspension_duration j R_j R_hp 0 (job_arrival j) +
      service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq
        higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j)
        (job_arrival j + d + 1) =
      service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq
        higher_eq_priority job_suspension_duration j R_j R_hp 0 (job_arrival j + d + 1) := by
    unfold service_of_other_hep_jobs_in_sched_jitter service_of_jobs
    rw [← Prosa.Util.Sum.list_sum_map_add]
    congr 1; apply List.map_congr_left; intro j0 _
    simp only [service_during]
    exact Finset.sum_Ico_consecutive
      (fun t => service_at (sched_jitter job_arrival job_task higher_eq_priority job_cost
        job_suspension_duration arr_seq j R_hp) j0 t)
      (by omega) (by omega)
  rw [h_combine]
  -- Apply service_equals_workload: w(0,arr_j+d+1) ≤ s(0,arr_j+d+1)
  exact jitter_reduction_service_equals_workload_in_jitter
    job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
    job_suspension_duration j R_j R_hp (job_arrival j + d + 1)
    (Nat.add_le_add_left (Nat.succ_le_of_lt H_d_lt_R) _)
    (by intro j_hp h_arrives h_before h_hep
        apply completion_monotonic (inflated_job_cost job_cost job_suspension_duration j)
          (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration
            arr_seq j R_hp) j_hp _ _ (Nat.le_succ _)
        apply H_all_jobs_completed_in_sched_jitter j_hp h_arrives h_hep
        simp only [jitter_has_passed, actual_arrival_before] at h_before ⊢
        exact Nat.lt_succ_iff.mp h_before)
include H_d_lt_R H_all_jobs_completed_in_sched_jitter
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
    H_valid_schedule H_from_arrival_sequence H_bounded_response_time_of_hp_jobs
    H_no_deadline_misses_for_previous_jobs in
theorem jitter_reduction_inductive_step_case1 : service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d + 1) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d + 1) := by
  have h1 := jitter_reduction_convert_service_to_workload job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent higher_eq_priority job_suspension_duration sched_susp
    H_valid_schedule j R_j d H_d_lt_R
  have h2 := jitter_reduction_compare_workload job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
    job_suspension_duration sched_susp j R_j R_hp d
  have h3 := jitter_reduction_compare_service task_period task_deadline job_arrival job_cost
    job_deadline job_task ts arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    H_jobs_from_taskset H_job_deadlines_equal_task_deadlines H_constrained_deadlines
    H_sporadic_arrivals higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j
    H_from_arrival_sequence R_j R_hp H_bounded_response_time_of_hp_jobs
    H_no_deadline_misses_for_previous_jobs d
  have h4 := jitter_reduction_convert_workload_to_service job_arrival job_cost job_task arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority
    job_suspension_duration j R_j R_hp d H_d_lt_R H_all_jobs_completed_in_sched_jitter
  exact le_trans h1 (le_trans h2 (le_trans h3 h4))
end NoPendingJobs
section ThereArePendingJobs
variable (H_there_are_pending_jobs_in_sched_jitter : ∃ j_hp, arrives_in arr_seq j_hp ∧ (higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j)) = true ∧ jitter_has_passed job_arrival (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp) j_hp (job_arrival j + d) ∧ ¬ completed_by (inflated_job_cost job_cost job_suspension_duration j) (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j_hp (job_arrival j + d))
include H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    H_valid_schedule H_from_arrival_sequence H_d_lt_R H_induction_hypothesis
    H_there_are_pending_jobs_in_sched_jitter in
theorem jitter_reduction_inductive_step_case2 : service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d + 1) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d + 1) := by
  set arr_j := job_arrival j
  set sched_j := sched_jitter job_arrival job_task higher_eq_priority job_cost
    job_suspension_duration arr_seq j R_hp
  set jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp
  -- Extract simple valid schedule conjunction for properties file compatibility
  have H_valid_props : jobs_come_from_arrival_sequence sched_susp arr_seq ∧
      jobs_must_arrive_to_execute job_arrival sched_susp ∧
      completed_jobs_dont_execute job_cost sched_susp ∧ True :=
    ⟨H_valid_schedule.1, H_valid_schedule.2.1, H_valid_schedule.2.2.1, trivial⟩
  -- Collect key properties of sched_jitter
  have WORKj := @sched_jitter_work_conserving _ _ _ _ job_arrival job_task arr_seq
    H_arrival_times_are_consistent higher_eq_priority job_cost job_suspension_duration j R_hp
  have RESPj := @sched_jitter_respects_policy _ _ _ _ job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    job_cost job_suspension_duration sched_susp H_valid_props j H_from_arrival_sequence R_hp
  have NOTj := @sched_jitter_does_not_pick_j _ _ _ _ job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset higher_eq_priority
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    job_cost job_suspension_duration sched_susp H_valid_props j H_from_arrival_sequence R_hp
  have AFTERj := sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq
    higher_eq_priority job_cost job_suspension_duration j R_hp
  have FROMj := @sched_jitter_jobs_come_from_arrival_sequence _ _ _ _ job_arrival job_task arr_seq
    H_arrival_times_are_consistent higher_eq_priority job_cost job_suspension_duration
    j H_from_arrival_sequence R_hp
  -- Unfold and split sums at arr_j + d
  unfold service_of_other_hep_jobs_in_sched_susp service_of_other_hep_jobs_in_sched_jitter
    service_of_jobs
  set L_s := (jobs_arrived_between arr_seq 0 (arr_j + R_j)).filter
    (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j))
  set L_j := (actual_arrivals_between job_arrival jj arr_seq 0 (arr_j + R_j)).filter
    (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j))
  -- Split service_during at arr_j + d: sum over [arr_j, arr_j+d+1) = sum over [arr_j, arr_j+d) + single slot
  have h_split : ∀ (s : schedule Job) (L : List Job),
      (L.map (fun j0 => service_during s j0 arr_j (arr_j + d + 1))).sum =
      (L.map (fun j0 => service_during s j0 arr_j (arr_j + d))).sum +
      (L.map (fun j0 => service_at s j0 (arr_j + d))).sum := by
    intro s L; rw [← Prosa.Util.Sum.list_sum_map_add]
    congr 1; apply List.map_congr_left; intro j0 _
    simp only [service_during]
    rw [← Finset.sum_Ico_succ_top (Nat.le_add_right arr_j d)]
  rw [h_split sched_susp L_s, h_split sched_j L_j]
  apply Nat.add_le_add
  · -- Prefix [arr_j, arr_j+d): exactly H_induction_hypothesis
    exact H_induction_hypothesis
  · -- Single point bound at time arr_j + d
    -- Extract the pending job from hypothesis
    obtain ⟨j1, h_arrives_1, h_hep_cond_1, h_jitter_1, h_not_comp_1⟩ :=
      H_there_are_pending_jobs_in_sched_jitter
    have h_cond := h_hep_cond_1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cond
    have h_hep_1 : higher_eq_priority (job_task j1) (job_task j) = true := h_cond.1
    have h_ne_1 : j1 ≠ j := h_cond.2
    -- Case: is any hep job scheduled in sched_susp at arr_j + d or not?
    by_cases h_zero : (L_s.map (fun j0 => service_at sched_susp j0 (arr_j + d))).sum = 0
    · -- No hep job contributes: LHS = 0 ≤ RHS
      omega
    · -- Some hep job(s) contribute: LHS ≥ 1
      -- Uniprocessor bound: LHS ≤ 1
      have h_lhs : (L_s.map (fun j0 => service_at sched_susp j0 (arr_j + d))).sum ≤ 1 := by
        have h_nodup : L_s.Nodup := List.Nodup.filter _
          (arrivals_uniq job_arrival arr_seq H_arrival_times_are_consistent
            H_arrival_sequence_is_a_set 0 (arr_j + R_j))
        suffices hgen : ∀ (M : List Job), M.Nodup →
            (M.map (fun j0 => service_at sched_susp j0 (arr_j + d))).sum ≤ 1 from hgen L_s h_nodup
        intro M hnd; induction M with
        | nil => simp
        | cons a M' ih =>
          simp only [List.map_cons, List.sum_cons]
          rw [List.nodup_cons] at hnd
          by_cases ha : scheduled_at sched_susp a (arr_j + d) = true
          · have h_one : service_at sched_susp a (arr_j + d) = 1 := by simp [service_at, ha]
            rw [h_one]
            suffices (M'.map (fun j0 => service_at sched_susp j0 (arr_j + d))).sum = 0 by omega
            apply List.sum_eq_zero; intro x hx; rw [List.mem_map] at hx
            obtain ⟨j0, hj0_mem, rfl⟩ := hx
            have hne : j0 ≠ a := fun h => hnd.1 (h ▸ hj0_mem)
            by_cases hj0 : scheduled_at sched_susp j0 (arr_j + d) = true
            · exact absurd (only_one_job_scheduled sched_susp a j0 (arr_j + d) ha hj0).symm hne
            · simp only [service_at]; cases h : scheduled_at sched_susp j0 (arr_j + d) <;> simp_all
          · have h_zero_a : service_at sched_susp a (arr_j + d) = 0 := by
              simp only [service_at]; cases h : scheduled_at sched_susp a (arr_j + d) <;> simp_all
            rw [h_zero_a, Nat.zero_add]; exact ih hnd.2
      -- Work conservation: RHS ≥ 1
      -- Find a job j2 scheduled in sched_jitter at arr_j + d
      have h_rhs : 1 ≤ (L_j.map (fun j0 => service_at sched_j j0 (arr_j + d))).sum := by
        by_cases h_sched_1 : scheduled_at sched_j j1 (arr_j + d) = true
        · -- j1 itself is scheduled in sched_jitter
          have h_j1_in : j1 ∈ L_j := by
            simp only [L_j]; rw [List.mem_filter]; exact ⟨
              arrived_between_implies_in_actual_arrivals job_arrival jj arr_seq
                H_arrival_times_are_consistent j1 0 (arr_j + R_j) h_arrives_1
                ⟨Nat.zero_le _, by
                  simp only [jitter_has_passed, actual_arrival] at h_jitter_1
                  exact Nat.lt_of_le_of_lt h_jitter_1
                    (Nat.add_lt_add_left H_d_lt_R (job_arrival j))⟩,
              h_hep_cond_1⟩
          calc 1 = service_at sched_j j1 (arr_j + d) := by
                  unfold service_at; rw [h_sched_1]; rfl
            _ ≤ (L_j.map (fun j0 => service_at sched_j j0 (arr_j + d))).sum :=
                List.le_sum_of_mem (List.mem_map.mpr ⟨j1, h_j1_in, rfl⟩)
        · -- j1 is not scheduled → j1 is backlogged → work conservation
          have h_back_1 : Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.backlogged
              job_arrival (inflated_job_cost job_cost job_suspension_duration j) jj sched_j
              j1 (arr_j + d) :=
            ⟨⟨h_jitter_1, h_not_comp_1⟩, h_sched_1⟩
          obtain ⟨j2, h_sched_2⟩ := WORKj j1 (arr_j + d) h_arrives_1 h_back_1
          -- j2 has priority ≥ j1 (respects_policy)
          have h_resp_2 : higher_eq_priority (job_task j2) (job_task j1) = true :=
            RESPj j1 j2 (arr_j + d) h_arrives_1 h_back_1 h_sched_2
          -- j2 has hep over j (transitivity)
          have h_hep_2 : higher_eq_priority (job_task j2) (job_task j) = true :=
            H_priority_is_transitive (job_task j1) (job_task j2) (job_task j) h_resp_2 h_hep_1
          -- j2 ≠ j (does_not_pick_j: pending hep j1 means j is NOT scheduled)
          have h_ne_2 : j2 ≠ j := by
            intro heq; subst heq
            exact NOTj j1 (arr_j + d) h_arrives_1 h_ne_1
              ⟨h_jitter_1, h_not_comp_1⟩ h_hep_1 h_sched_2
          -- j2 comes from arrival sequence
          have h_arrives_2 : arrives_in arr_seq j2 := FROMj j2 (arr_j + d) h_sched_2
          -- j2 ∈ L_j
          have h_j2_in : j2 ∈ L_j := by
            simp only [L_j]; rw [List.mem_filter]; constructor
            · exact arrived_between_implies_in_actual_arrivals job_arrival jj arr_seq
                H_arrival_times_are_consistent j2 0 (arr_j + R_j) h_arrives_2
                ⟨Nat.zero_le _, by
                  have := AFTERj j2 (arr_j + d) h_sched_2
                  simp only [jitter_has_passed, actual_arrival] at this
                  exact Nat.lt_of_le_of_lt this
                    (Nat.add_lt_add_left H_d_lt_R (job_arrival j))⟩
            · simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨h_hep_2, h_ne_2⟩
          calc 1 = service_at sched_j j2 (arr_j + d) := by
                  unfold service_at
                  have h_sched_2' : scheduled_at sched_j j2 (arr_j + d) = true := h_sched_2
                  rw [h_sched_2']; rfl
            _ ≤ (L_j.map (fun j0 => service_at sched_j j0 (arr_j + d))).sum :=
                List.le_sum_of_mem (List.mem_map.mpr ⟨j2, h_j2_in, rfl⟩)
      omega
end ThereArePendingJobs
end InductiveStep
include ts H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    H_valid_schedule H_from_arrival_sequence
    task_period task_deadline job_deadline
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
    H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs in
theorem jitter_reduction_more_service_inside_the_interval : ∀ d, d ≤ R_j → service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + d) ≤ service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + d) := by
  intro d hd
  induction d with
  | zero =>
    simp only [Nat.add_zero]
    unfold service_of_other_hep_jobs_in_sched_susp service_of_other_hep_jobs_in_sched_jitter
      service_of_jobs service_during
    simp only [Finset.Ico_self, Finset.sum_empty, List.map_const', List.sum_replicate,
      Nat.smul_one_eq_cast, Nat.zero_mul, smul_zero, le_refl]
  | succ n ih =>
    have ih' := ih (Nat.le_of_succ_le hd)
    have h_n_lt : n < R_j := Nat.lt_of_succ_le hd
    by_cases H_pending : ∃ j_hp, arrives_in arr_seq j_hp ∧
        (higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j)) = true ∧
        jitter_has_passed job_arrival
          (job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp)
          j_hp (job_arrival j + n) ∧
        ¬ completed_by (inflated_job_cost job_cost job_suspension_duration j)
          (sched_jitter job_arrival job_task higher_eq_priority job_cost
            job_suspension_duration arr_seq j R_hp)
          j_hp (job_arrival j + n)
    · exact @jitter_reduction_inductive_step_case2 _ _ _ _
        job_arrival job_cost job_task ts arr_seq
        H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
        higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
        job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence
        R_j R_hp n h_n_lt ih' H_pending
    · push_neg at H_pending
      exact @jitter_reduction_inductive_step_case1 _ _ task_period task_deadline _ _
        job_arrival job_cost job_deadline job_task ts arr_seq
        H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
        H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
        higher_eq_priority job_suspension_duration sched_susp H_valid_schedule
        j H_from_arrival_sequence R_j R_hp
        H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs
        n h_n_lt H_pending
end MoreServiceInsideTheInterval
end MoreServiceAfterArrival
section JitterAwareScheduleIsWorse
include H_arrival_times_are_consistent H_arrival_sequence_is_a_set in
theorem jitter_reduction_service_jitter : service_during (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j (job_arrival j) (job_arrival j + R_j) ≤ R_j - service_of_other_hep_jobs_in_sched_jitter job_arrival job_cost job_task arr_seq higher_eq_priority job_suspension_duration j R_j R_hp (job_arrival j) (job_arrival j + R_j) := by
  set sched_j := sched_jitter job_arrival job_task higher_eq_priority job_cost
    job_suspension_duration arr_seq j R_hp
  set jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp
  set arr_j := job_arrival j
  apply Prosa.Util.Nat.subh3
  simp only [service_during, service_of_other_hep_jobs_in_sched_jitter, service_of_jobs]
  set L := (actual_arrivals_between job_arrival jj arr_seq 0 (arr_j + R_j)).filter
    (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j))
  -- Swap sums: Σ_j Σ_t → Σ_t Σ_j
  have h_swap : (L.map (fun j0 => ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
      service_at sched_j j0 t)).sum =
      ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
        (L.map (fun j0 => service_at sched_j j0 t)).sum := by
    suffices hkey : ∀ (M : List Job), (M.map (fun j0 => ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
        service_at sched_j j0 t)).sum =
        ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
          (M.map (fun j0 => service_at sched_j j0 t)).sum from hkey L
    intro M; induction M with
    | nil => simp
    | cons a M' ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]
  rw [h_swap, ← Finset.sum_add_distrib]
  -- Per-slot bound: ∀ t, service_at j t + Σ_{j0 ∈ L} service_at j0 t ≤ 1
  -- Bound by ∑ 1 = R_j
  calc ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
        (service_at sched_j j t + (L.map (fun j0 => service_at sched_j j0 t)).sum)
      ≤ ∑ t ∈ Finset.Ico arr_j (arr_j + R_j), 1 := by
        apply Finset.sum_le_sum; intro t _
        -- Per-slot: service_at j t + list_sum ≤ 1
        -- Case analysis on sched_j t
        cases h_sched_t : sched_j t with
        | none =>
          have h_sa : ∀ j0, service_at sched_j j0 t = 0 := fun j0 => by
            simp only [service_at, scheduled_at, h_sched_t]; rfl
          simp [h_sa]
        | some j' =>
          by_cases hj' : j' = j
          · -- j' = j: service_at j t = 1, others = 0
            have h_j_sa : service_at sched_j j t = 1 := by
              simp only [service_at, scheduled_at, h_sched_t, hj', beq_self_eq_true]; rfl
            rw [h_j_sa]
            suffices (L.map (fun j0 => service_at sched_j j0 t)).sum = 0 from by omega
            apply List.sum_eq_zero; intro x hx
            rw [List.mem_map] at hx; obtain ⟨j0, hj0, rfl⟩ := hx
            have hne : j0 ≠ j := by
              rw [List.mem_filter] at hj0
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hj0; exact hj0.2.2
            simp only [service_at, scheduled_at, h_sched_t]
            have : (some j' == some j0) = false := by
              rw [hj']; simp [beq_eq_false_iff_ne.mpr (Ne.symm hne)]
            simp [this]
          · have h_j_sa : service_at sched_j j t = 0 := by
              simp only [service_at, scheduled_at, h_sched_t,
                show (some j' == some j) = (j' == j) from rfl,
                beq_eq_false_iff_ne.mpr hj', Bool.toNat_false]
            rw [h_j_sa, Nat.zero_add]
            -- Show: list sum ≤ 1 (uniprocessor: at most one job scheduled)
            have h_nodup : L.Nodup := List.Nodup.filter _
              (actual_arrivals_uniq job_arrival jj arr_seq
                H_arrival_times_are_consistent H_arrival_sequence_is_a_set 0 (arr_j + R_j))
            suffices hgen : ∀ (M : List Job), M.Nodup →
                (M.map (fun j0 => service_at sched_j j0 t)).sum ≤ 1 from hgen L h_nodup
            intro M hnd; induction M with
            | nil => simp
            | cons a M' ih =>
              simp only [List.map_cons, List.sum_cons]
              rw [List.nodup_cons] at hnd
              by_cases ha : scheduled_at sched_j a t = true
              · have h_one : service_at sched_j a t = 1 := by
                  simp [service_at, ha]
                rw [h_one]
                suffices (M'.map (fun j0 => service_at sched_j j0 t)).sum = 0 from by omega
                apply List.sum_eq_zero; intro x hx
                rw [List.mem_map] at hx; obtain ⟨j0, hj0_mem, rfl⟩ := hx
                have hne : j0 ≠ a := fun h => hnd.1 (h ▸ hj0_mem)
                simp only [service_at]
                by_cases hj0 : scheduled_at sched_j j0 t = true
                · exact absurd (only_one_job_scheduled sched_j a j0 t ha hj0).symm hne
                · simp only [scheduled_at] at hj0 ⊢
                  cases h : sched_j t == some j0 <;> simp_all
              · have h_zero : service_at sched_j a t = 0 := by
                  simp only [service_at]; cases h : scheduled_at sched_j a t <;> simp_all
                rw [h_zero, Nat.zero_add]; exact ih hnd.2
    _ = R_j := by simp [Finset.sum_const, smul_eq_mul]
section JobNotCompleted
variable (H_j_not_completed : ¬ completed_by job_cost sched_susp j (job_arrival j + R_j))
include H_j_not_completed H_valid_schedule H_from_arrival_sequence
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set in
theorem jitter_reduction_service_susp : R_j - service_of_other_hep_jobs_in_sched_susp job_arrival job_task arr_seq higher_eq_priority sched_susp j R_j (job_arrival j) (job_arrival j + R_j) ≤ service_during sched_susp j (job_arrival j) (job_arrival j + R_j) + cumulative_suspension_during job_arrival job_cost job_suspension_duration sched_susp j (job_arrival j) (job_arrival j + R_j) := by
  classical
  have ⟨FROMarr, MUSTARRs, COMPs, WORK_raw, PRIO_raw, SELF⟩ := H_valid_schedule
  set arr_j := job_arrival j
  -- Rearrange: R_j ≤ service_j + susp + service_hep
  rw [Nat.sub_le_iff_le_add]
  simp only [service_during, cumulative_suspension_during, service_of_other_hep_jobs_in_sched_susp,
    service_of_jobs]
  set L := (jobs_arrived_between arr_seq 0 (arr_j + R_j)).filter
    (fun j_hp => higher_eq_priority (job_task j_hp) (job_task j) && decide (j_hp ≠ j))
  -- Swap sums for service_hep
  have h_swap : (L.map (fun j0 => ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
      service_at sched_susp j0 t)).sum =
      ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
        (L.map (fun j0 => service_at sched_susp j0 t)).sum := by
    suffices hkey : ∀ (M : List Job), (M.map (fun j0 => ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
        service_at sched_susp j0 t)).sum =
        ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
          (M.map (fun j0 => service_at sched_susp j0 t)).sum from hkey L
    intro M; induction M with
    | nil => simp
    | cons a M' ih => simp only [List.map_cons, List.sum_cons, ih, Finset.sum_add_distrib]
  rw [h_swap, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  -- R_j = ∑ 1
  calc R_j = ∑ _ ∈ Finset.Ico arr_j (arr_j + R_j), 1 := by
        simp [Finset.sum_const, smul_eq_mul]
    _ ≤ ∑ t ∈ Finset.Ico arr_j (arr_j + R_j),
          (service_at sched_susp j t +
           (if suspended_at job_arrival job_cost job_suspension_duration sched_susp j t then 1 else 0) +
           (L.map (fun j0 => service_at sched_susp j0 t)).sum) := by
        apply Finset.sum_le_sum; intro t ht
        rw [Finset.mem_Ico] at ht
        -- Per-slot: 1 ≤ service_at j t + susp_indicator t + hep_service t
        by_cases hsusp : suspended_at job_arrival job_cost job_suspension_duration sched_susp j t
        · -- Case 1: j is suspended → indicator = 1 → sum ≥ 1
          rw [if_pos hsusp]
          exact le_trans (Nat.le_add_left 1 _) (Nat.le_add_right _ _)
        · -- j not suspended → indicator = 0
          rw [if_neg hsusp, Nat.add_zero]
          by_cases hsched : scheduled_at sched_susp j t = true
          · -- Case 2: j is scheduled → service_at j t = 1 → sum ≥ 1
            have : service_at sched_susp j t = 1 := by simp [service_at, hsched]
            rw [this]; exact Nat.le_add_right 1 _
          · -- Case 3: backlogged → work conservation → hep job scheduled → sum ≥ 1
            have h_not_comp_t : ¬ completed_by job_cost sched_susp j t := by
              intro hcomp; exact H_j_not_completed
                (completion_monotonic job_cost sched_susp j t (arr_j + R_j) (le_of_lt ht.2) hcomp)
            have h_arrived : has_arrived job_arrival j t := ht.1
            have ⟨j_hp, hSCHED_hp⟩ := WORK_raw j t H_from_arrival_sequence
              ⟨⟨h_arrived, h_not_comp_t⟩, hsched, hsusp⟩
            have h_sa_hp : service_at sched_susp j_hp t = 1 := by simp [service_at, hSCHED_hp]
            have h_ge : 1 ≤ (L.map (fun j0 => service_at sched_susp j0 t)).sum := by
              rw [← h_sa_hp]
              suffices ∀ (M : List Job) (x : Job), x ∈ M →
                  service_at sched_susp x t ≤
                  (M.map (fun j0 => service_at sched_susp j0 t)).sum from this L j_hp (by
                rw [List.mem_filter]; constructor
                · exact arrived_between_implies_in_arrivals job_arrival arr_seq
                    H_arrival_times_are_consistent j_hp 0 (arr_j + R_j)
                    (FROMarr j_hp t hSCHED_hp)
                    ⟨Nat.zero_le _, by
                      have := MUSTARRs j_hp t hSCHED_hp
                      unfold has_arrived at this; exact lt_of_le_of_lt this ht.2⟩
                · simp only [Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨PRIO_raw j j_hp t H_from_arrival_sequence
                    ⟨⟨h_arrived, h_not_comp_t⟩, hsched, hsusp⟩ hSCHED_hp,
                    fun heq => hsched (heq ▸ hSCHED_hp)⟩)
              intro M x hx; induction M with
              | nil => simp at hx
              | cons a M' ih =>
                simp only [List.map_cons, List.sum_cons]
                rcases List.mem_cons.mp hx with rfl | h
                · exact Nat.le_add_right _ _
                · exact le_trans (ih h) (Nat.le_add_left _ _)
            exact le_trans h_ge (Nat.le_add_left _ _)
include H_j_not_completed H_valid_schedule H_from_arrival_sequence
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    ts H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    task_period task_deadline job_deadline
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
    H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs in
theorem jitter_reduction_less_service_for_job_j : service_during (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j (job_arrival j) (job_arrival j + R_j) ≤ service_during sched_susp j (job_arrival j) (job_arrival j + R_j) + cumulative_suspension_during job_arrival job_cost job_suspension_duration sched_susp j (job_arrival j) (job_arrival j + R_j) := by
  have h1 := jitter_reduction_service_jitter job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration j R_j R_hp
  have h2 := jitter_reduction_more_service_inside_the_interval task_period task_deadline
    job_arrival job_cost job_deadline job_task ts arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
    higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    job_suspension_duration sched_susp H_valid_schedule
    j H_from_arrival_sequence R_j R_hp
    H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs R_j le_rfl
  have h3 := Nat.sub_le_sub_left h2 R_j
  have h4 := jitter_reduction_service_susp job_arrival job_cost job_task arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set higher_eq_priority job_suspension_duration sched_susp H_valid_schedule j H_from_arrival_sequence R_j H_j_not_completed
  exact le_trans h1 (le_trans h3 h4)
end JobNotCompleted
variable (H_response_time_of_j_in_sched_jitter : is_response_time_bound_of_job job_arrival (inflated_job_cost job_cost job_suspension_duration j) (sched_jitter job_arrival job_task higher_eq_priority job_cost job_suspension_duration arr_seq j R_hp) j R_j)
include H_valid_schedule H_from_arrival_sequence H_arrival_times_are_consistent
    H_arrival_sequence_is_a_set H_response_time_of_j_in_sched_jitter
    ts H_jobs_from_taskset H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    task_period task_deadline job_deadline
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
    H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs in
theorem jitter_reduction_job_j_completes_no_later : is_response_time_bound_of_job job_arrival job_cost sched_susp j R_j := by
  by_contra h_not; apply h_not
  -- Goal: is_response_time_bound_of_job = completed_by job_cost sched_susp j (arr_j + R_j)
  have ⟨_, MUSTARRs, COMPs, _, _, SELF⟩ := H_valid_schedule
  -- Service bound from jitter reduction
  have h_less := @jitter_reduction_less_service_for_job_j _ _ task_period task_deadline _ _
    job_arrival job_cost job_deadline job_task ts arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
    higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    job_suspension_duration sched_susp H_valid_schedule
    j H_from_arrival_sequence R_j R_hp
    H_bounded_response_time_of_hp_jobs H_no_deadline_misses_for_previous_jobs h_not
  -- Setup: sched_jitter abbreviations
  set sched_j := sched_jitter job_arrival job_task higher_eq_priority job_cost
    job_suspension_duration arr_seq j R_hp
  set jj := job_jitter job_arrival job_task higher_eq_priority job_cost j R_hp
  have h_exec : jobs_execute_after_jitter job_arrival jj sched_j :=
    sched_jitter_jobs_execute_after_jitter job_arrival job_task arr_seq higher_eq_priority
      job_cost job_suspension_duration j R_hp
  -- jitter of j is 0 (j has same task as itself)
  have h_jit_j : jj j = 0 := by
    simp [jj, job_jitter]
  -- No service before arr_j in sched_jitter (actual_arrival j = arr_j)
  have h_zero : ∑ i ∈ Finset.Ico 0 (job_arrival j), service_at sched_j j i = 0 :=
    cumulative_service_before_jitter_is_zero job_arrival jj sched_j h_exec j 0 (job_arrival j)
      (by simp [actual_arrival, h_jit_j])
  -- service = service_during 0 t = 0 + service_during arr_j t = service_during arr_j t
  have h_svc_eq : service sched_j j (job_arrival j + R_j) =
      service_during sched_j j (job_arrival j) (job_arrival j + R_j) := by
    simp only [service, service_during]
    rw [(Finset.sum_Ico_consecutive (fun t => service_at sched_j j t)
      (Nat.zero_le _) (Nat.le_add_right _ _)).symm, h_zero, Nat.zero_add]
  -- inflated_cost j j = cost j + total_susp j
  have h_inf : inflated_job_cost job_cost job_suspension_duration j j =
      job_cost j + total_suspension job_cost job_suspension_duration j := by
    simp [inflated_job_cost]
  -- Response time bound gives: cost + total_susp ≤ service_during sched_j arr_j (arr_j + R_j)
  have h1 : job_cost j + total_suspension job_cost job_suspension_duration j ≤
      service_during sched_j j (job_arrival j) (job_arrival j + R_j) := by
    rw [← h_inf, ← h_svc_eq]; exact H_response_time_of_j_in_sched_jitter
  -- Cumulative suspension ≤ total suspension
  have h_susp := cumulative_suspension_le_total_suspension job_arrival job_cost
    job_suspension_duration sched_susp j MUSTARRs COMPs SELF
    (job_arrival j) (job_arrival j + R_j)
  -- Chain: cost + total_susp ≤ sd_j ≤ sd_susp + cumul ≤ sd_susp + total_susp
  have h2 : job_cost j + total_suspension job_cost job_suspension_duration j ≤
      service_during sched_susp j (job_arrival j) (job_arrival j + R_j) +
      total_suspension job_cost job_suspension_duration j :=
    le_trans h1 (le_trans h_less (Nat.add_le_add_left h_susp _))
  -- Cancel total_susp
  have h3 : job_cost j ≤ service_during sched_susp j (job_arrival j) (job_arrival j + R_j) :=
    Nat.le_of_add_le_add_right h2
  -- service_during arr_j ≤ service_during 0 = service
  show completed_by job_cost sched_susp j (job_arrival j + R_j)
  unfold completed_by
  exact le_trans h3 (by
    simp only [service, service_during]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Ico_subset_Ico (Nat.zero_le _) le_rfl)
      (fun _ _ _ => Nat.zero_le _))
end JitterAwareScheduleIsWorse
end ProvingScheduleProperties
end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule_service
end
