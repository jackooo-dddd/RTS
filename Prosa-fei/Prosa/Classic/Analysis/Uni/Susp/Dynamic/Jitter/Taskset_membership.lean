-- Translated from: ../rt-proofs/classic/analysis/uni/susp/dynamic/jitter/taskset_membership.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Valid_schedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_taskset_generation
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction_properties

noncomputable section

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Taskset_membership

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Model.Schedule.Uni.Susp.Valid_schedule
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule.JitterScheduleConstruction
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_taskset_generation.JitterTaskSetGeneration
open Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction.SustainabilitySingleCost
open Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction_properties.SustainabilitySingleCostProperties
open Prosa.Classic.Util.Pick

namespace TaskSetMembership

section ProvingMembership

variable {Task : Type _} [DecidableEq Task]
variable (task_period : Task → Time)
variable (task_deadline : Task → Time)
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → Task)

variable (ts : List Task)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent :
  arrival_times_are_consistent job_arrival arr_seq)
variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)

variable (H_jobs_come_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (job_cost : Job → Time)
variable (task_cost : Task → Time)

variable (job_suspension_duration : job_suspension Job)
variable (task_suspension_bound : Task → Time)

variable (higher_eq_priority : FP_policy Task)
variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
variable (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)

variable (sched_susp : schedule Job)
variable (H_valid_schedule :
  valid_suspension_aware_schedule job_arrival arr_seq
    (FP_to_JLDP job_task higher_eq_priority)
    job_suspension_duration job_cost sched_susp)

variable (tsk_i : Task)
variable (H_tsk_in_ts : tsk_i ∈ ts)

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk_i : job_task j = tsk_i)

variable (R : Task → Time)
variable (H_valid_response_time_bound_of_hp_tasks_in_all_schedules :
  ∀ (jc : Job → Time) (s : schedule Job),
    valid_suspension_aware_schedule job_arrival arr_seq
      (FP_to_JLDP job_task higher_eq_priority)
      job_suspension_duration jc s →
    ∀ tsk_hp,
      tsk_hp ∈ ts →
      (higher_eq_priority tsk_hp tsk_i && decide (tsk_hp ≠ tsk_i)) = true →
      is_response_time_bound_of_task job_arrival jc job_task arr_seq s tsk_hp (R tsk_hp))

def actual_response_time (j_hp : Job) : Time :=
  pick_min (R (job_task j_hp) + 1)
    (fun r => decide (job_cost j_hp ≤ service sched_susp j_hp (job_arrival j_hp + r)))

include H_valid_schedule H_jobs_come_from_taskset
  H_valid_response_time_bound_of_hp_tasks_in_all_schedules in
theorem actual_response_time_is_valid :
    ∀ j_hp,
      arrives_in arr_seq j_hp →
      (higher_eq_priority (job_task j_hp) tsk_i && decide (job_task j_hp ≠ tsk_i)) = true →
      is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp
        (actual_response_time job_arrival job_task job_cost sched_susp R j_hp) := by
  intro j_hp ARRhp HP
  unfold actual_response_time
  apply pick_min_holds
  · exact ⟨R (job_task j_hp), Nat.lt_succ_of_le (le_refl _),
      decide_eq_true
        (H_valid_response_time_bound_of_hp_tasks_in_all_schedules job_cost sched_susp
         H_valid_schedule (job_task j_hp) (H_jobs_come_from_taskset j_hp ARRhp) HP
         j_hp ARRhp rfl)⟩
  · intro x _ hpx _
    have h := of_decide_eq_true hpx
    exact h

include H_valid_schedule H_jobs_come_from_taskset
  H_valid_response_time_bound_of_hp_tasks_in_all_schedules in
theorem actual_response_time_is_minimum :
    ∀ j_hp r_hp,
      arrives_in arr_seq j_hp →
      (higher_eq_priority (job_task j_hp) tsk_i && decide (job_task j_hp ≠ tsk_i)) = true →
      is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp r_hp →
      actual_response_time job_arrival job_task job_cost sched_susp R j_hp ≤ r_hp := by
  intro j_hp r_hp ARRhp HP RESP
  have EX : ∃ x, x < R (job_task j_hp) + 1 ∧
      (fun r => decide (job_cost j_hp ≤ service sched_susp j_hp (job_arrival j_hp + r))) x = true :=
    ⟨R (job_task j_hp), Nat.lt_succ_of_le (le_refl _),
      decide_eq_true
        (H_valid_response_time_bound_of_hp_tasks_in_all_schedules job_cost sched_susp
         H_valid_schedule (job_task j_hp) (H_jobs_come_from_taskset j_hp ARRhp) HP
         j_hp ARRhp rfl)⟩
  by_cases h : r_hp ≤ R (job_task j_hp)
  · -- Case: r_hp ≤ R(tsk_hp) — use pick_min_holds with minimality
    unfold actual_response_time
    exact pick_min_holds _ _ (fun x => x ≤ r_hp) EX
      (fun x _ _ MINx => MINx r_hp (Nat.lt_succ_of_le h) (decide_eq_true RESP))
  · -- Case: r_hp > R(tsk_hp) — use pick_min_ltn
    push_neg at h
    unfold actual_response_time
    exact le_trans (Nat.lt_succ_iff.mp (pick_min_ltn _ _ EX)) (le_of_lt h)

variable (H_positive_costs :
  ∀ j, arrives_in arr_seq j → job_cost j > 0)
variable (H_job_cost_le_task_cost :
  ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))
variable (H_dynamic_suspensions :
  dynamic_suspension_model job_cost job_task job_suspension_duration task_suspension_bound)

section JobCostPositive

include H_positive_costs in
theorem ts_membership_inflated_job_cost_positive :
    ∀ j_x, arrives_in arr_seq j_x →
      inflated_job_cost job_cost job_suspension_duration j j_x > 0 := by
  intro j_x ARR_x
  have h_cost := H_positive_costs j_x ARR_x
  simp only [inflated_job_cost]
  split
  · exact Nat.lt_of_lt_of_le h_cost (Nat.le_add_right _ _)
  · exact h_cost

end JobCostPositive

section JobCostBoundedByTaskCost

include H_job_cost_le_task_cost H_dynamic_suspensions H_j_arrives H_job_of_tsk_i in
theorem ts_membership_inflated_job_cost_le_inflated_task_cost :
    ∀ j_x, arrives_in arr_seq j_x →
      inflated_job_cost job_cost job_suspension_duration j j_x ≤
        inflated_task_cost task_cost task_suspension_bound tsk_i (job_task j_x) := by
  intro j_x ARR_x
  simp only [inflated_job_cost, inflated_task_cost]
  split
  · -- j_x == j: both costs inflated
    rename_i h_eq
    have h_eq' : j_x = j := beq_iff_eq.mp h_eq
    rw [h_eq']
    -- job_task j = tsk_i, so (job_task j == tsk_i) = true
    have htsk : (job_task j == tsk_i) = true := beq_iff_eq.mpr H_job_of_tsk_i
    rw [htsk]; simp
    exact Nat.add_le_add
      (H_job_cost_le_task_cost j H_j_arrives)
      (H_dynamic_suspensions j)
  · -- j_x ≠ j: only job_cost j_x
    split
    · -- job_task j_x == tsk_i
      exact le_trans (H_job_cost_le_task_cost j_x ARR_x) (Nat.le_add_right _ _)
    · -- job_task j_x ≠ tsk_i
      exact H_job_cost_le_task_cost j_x ARR_x

end JobCostBoundedByTaskCost

section JobJitterBoundedByTaskJitter

variable (any_j : Job)
variable (H_any_j_arrives : arrives_in arr_seq any_j)

section JitterOfHigherPriorityJobs

variable (H_higher_priority : higher_eq_priority (job_task any_j) tsk_i = true)
variable (H_different_task : decide (job_task any_j ≠ tsk_i) = true)

def higher_cost_wcet
    (job_cost : Job → Time) (task_cost : Task → Time)
    (job_task : Job → Task) (any_j : Job) (j_x : Job) : Time :=
  if j_x == any_j then task_cost (job_task any_j) else job_cost j_x

include H_valid_schedule H_jobs_come_from_taskset
  H_valid_response_time_bound_of_hp_tasks_in_all_schedules
  H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
  H_arrival_times_are_consistent H_any_j_arrives H_job_cost_le_task_cost in
theorem response_time_bound_in_sched_susp_highercost :
    let hcw := higher_cost_wcet job_cost task_cost job_task any_j
    ∀ tsk_hp,
      tsk_hp ∈ ts →
      (higher_eq_priority tsk_hp tsk_i && decide (tsk_hp ≠ tsk_i)) = true →
      is_response_time_bound_of_task job_arrival
        hcw
        job_task arr_seq
        (sched_susp_highercost job_arrival arr_seq
          (FP_to_JLDP job_task higher_eq_priority) sched_susp
          job_suspension_duration hcw)
        tsk_hp (R tsk_hp) := by
  intro hcw tsk_hp IN HP
  set jldp := FP_to_JLDP job_task higher_eq_priority with jldp_def
  have h_from := H_valid_schedule.1
  have h_arr := H_valid_schedule.2.1
  have h_comp := H_valid_schedule.2.2.1
  have h_wc := H_valid_schedule.2.2.2.1
  have h_resp := H_valid_schedule.2.2.2.2.1
  have h_self := H_valid_schedule.2.2.2.2.2
  have h_refl : JLDP_is_reflexive jldp :=
    fun t x => H_priority_is_reflexive (job_task x)
  have h_trans : JLDP_is_transitive jldp :=
    fun t y x z hxy hyz =>
      H_priority_is_transitive (job_task y) (job_task x) (job_task z) hxy hyz
  have h_total : JLDP_is_total arr_seq jldp :=
    fun j1 j2 t h1 h2 =>
      H_priority_is_total (job_task j1) (job_task j2)
        (H_jobs_come_from_taskset j1 h1) (H_jobs_come_from_taskset j2 h2)
  have h_cost_incr : hcw any_j ≥ job_cost any_j := by
    show higher_cost_wcet job_cost task_cost job_task any_j any_j ≥ job_cost any_j
    unfold higher_cost_wcet; split
    · exact H_job_cost_le_task_cost any_j H_any_j_arrives
    · exact le_refl _
  have h_only_j : ∀ j', j' ≠ any_j → hcw j' = job_cost j' := by
    intro j' h_ne
    show higher_cost_wcet job_cost task_cost job_task any_j j' = job_cost j'
    unfold higher_cost_wcet; split
    · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) h_ne
    · rfl
  apply H_valid_response_time_bound_of_hp_tasks_in_all_schedules hcw _ _ tsk_hp IN HP
  exact ⟨
    sched_susp_highercost_jobs_come_from_arrival_sequence
      job_arrival job_cost arr_seq H_arrival_times_are_consistent
      jldp h_refl h_trans h_total sched_susp h_from
      job_suspension_duration h_arr h_comp h_wc h_resp h_self
      any_j hcw h_cost_incr h_only_j,
    sched_susp_highercost_jobs_must_arrive_to_execute
      job_arrival job_cost arr_seq H_arrival_times_are_consistent
      jldp h_refl h_trans h_total sched_susp h_from
      job_suspension_duration h_arr h_comp h_wc h_resp h_self
      any_j hcw h_cost_incr h_only_j,
    sched_susp_highercost_completed_jobs_dont_execute
      job_arrival job_cost arr_seq H_arrival_times_are_consistent
      jldp h_refl h_trans h_total sched_susp h_from
      job_suspension_duration h_arr h_comp h_wc h_resp h_self
      any_j hcw h_cost_incr h_only_j,
    sched_susp_highercost_work_conserving
      job_arrival job_cost arr_seq H_arrival_times_are_consistent
      jldp h_refl h_trans h_total sched_susp h_from
      job_suspension_duration h_arr h_comp h_wc h_resp h_self
      any_j hcw h_cost_incr h_only_j,
    sched_susp_highercost_respects_policy
      job_arrival job_cost arr_seq H_arrival_times_are_consistent
      jldp h_refl h_trans h_total sched_susp h_from
      job_suspension_duration h_arr h_comp h_wc h_resp h_self
      any_j hcw h_cost_incr h_only_j,
    sched_susp_highercost_respects_self_suspensions
      job_arrival job_cost arr_seq H_arrival_times_are_consistent
      jldp h_refl h_trans h_total sched_susp h_from
      job_suspension_duration h_arr h_comp h_wc h_resp h_self
      any_j hcw h_cost_incr h_only_j⟩

include H_valid_schedule H_jobs_come_from_taskset
  H_valid_response_time_bound_of_hp_tasks_in_all_schedules
  H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
  H_arrival_times_are_consistent H_any_j_arrives H_job_cost_le_task_cost
  H_positive_costs H_higher_priority H_different_task in
theorem ts_membership_difference_in_response_times :
    actual_response_time job_arrival job_task job_cost sched_susp R any_j - job_cost any_j ≤
      R (job_task any_j) - task_cost (job_task any_j) := by
  set hcw := higher_cost_wcet job_cost task_cost job_task any_j with hcw_def
  set jldp := FP_to_JLDP job_task higher_eq_priority with jldp_def
  set art := actual_response_time job_arrival job_task job_cost sched_susp R any_j with art_def
  -- HP condition for any_j
  have HP_any : (higher_eq_priority (job_task any_j) tsk_i && decide (job_task any_j ≠ tsk_i)) = true := by
    simp only [Bool.and_eq_true]; exact ⟨H_higher_priority, H_different_task⟩
  -- Extract valid schedule components
  have h_from := H_valid_schedule.1
  have h_arr := H_valid_schedule.2.1
  have h_comp := H_valid_schedule.2.2.1
  have h_wc := H_valid_schedule.2.2.2.1
  have h_resp := H_valid_schedule.2.2.2.2.1
  have h_self := H_valid_schedule.2.2.2.2.2
  have h_refl : JLDP_is_reflexive jldp :=
    fun t x => H_priority_is_reflexive (job_task x)
  have h_trans : JLDP_is_transitive jldp :=
    fun t y x z hxy hyz =>
      H_priority_is_transitive (job_task y) (job_task x) (job_task z) hxy hyz
  have h_total : JLDP_is_total arr_seq jldp :=
    fun j1 j2 t h1 h2 =>
      H_priority_is_total (job_task j1) (job_task j2)
        (H_jobs_come_from_taskset j1 h1) (H_jobs_come_from_taskset j2 h2)
  have h_cost_incr : hcw any_j ≥ job_cost any_j := by
    show higher_cost_wcet job_cost task_cost job_task any_j any_j ≥ job_cost any_j
    unfold higher_cost_wcet; split
    · exact H_job_cost_le_task_cost any_j H_any_j_arrives
    · exact le_refl _
  have h_only_j : ∀ j', j' ≠ any_j → hcw j' = job_cost j' := by
    intro j' h_ne
    show higher_cost_wcet job_cost task_cost job_task any_j j' = job_cost j'
    unfold higher_cost_wcet; split
    · rename_i h_eq; exact absurd (beq_iff_eq.mp h_eq) h_ne
    · rfl
  have hcw_eq : hcw any_j = task_cost (job_task any_j) := by
    show higher_cost_wcet job_cost task_cost job_task any_j any_j = task_cost (job_task any_j)
    unfold higher_cost_wcet; split
    · rfl
    · rename_i h; exact absurd (beq_self_eq_true any_j) h
  -- Response time bounds from same-section theorems
  have h_resp_valid : is_response_time_bound_of_job job_arrival job_cost sched_susp any_j art :=
    actual_response_time_is_valid
      job_arrival job_task ts arr_seq H_jobs_come_from_taskset
      job_cost job_suspension_duration higher_eq_priority sched_susp H_valid_schedule
      tsk_i R H_valid_response_time_bound_of_hp_tasks_in_all_schedules
      any_j H_any_j_arrives HP_any
  have h_resp_tight : ∀ r', is_response_time_bound_of_job job_arrival job_cost sched_susp any_j r' →
      art ≤ r' :=
    fun r' hr' => actual_response_time_is_minimum
      job_arrival job_task ts arr_seq H_jobs_come_from_taskset
      job_cost job_suspension_duration higher_eq_priority sched_susp H_valid_schedule
      tsk_i R H_valid_response_time_bound_of_hp_tasks_in_all_schedules
      any_j r' H_any_j_arrives HP_any hr'
  have h_resp_hc : is_response_time_bound_of_job job_arrival hcw
      (sched_susp_highercost job_arrival arr_seq jldp sched_susp job_suspension_duration hcw)
      any_j (R (job_task any_j)) :=
    response_time_bound_in_sched_susp_highercost
      job_arrival job_task ts arr_seq H_arrival_times_are_consistent H_jobs_come_from_taskset
      job_cost task_cost job_suspension_duration higher_eq_priority
      H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
      sched_susp H_valid_schedule tsk_i R H_valid_response_time_bound_of_hp_tasks_in_all_schedules
      H_job_cost_le_task_cost any_j H_any_j_arrives
      (job_task any_j) (H_jobs_come_from_taskset any_j H_any_j_arrives) HP_any
      any_j H_any_j_arrives rfl
  calc art - job_cost any_j
      ≤ R (job_task any_j) - hcw any_j :=
        sched_susp_highercost_incurs_more_interference
          job_arrival job_cost arr_seq H_arrival_times_are_consistent
          jldp h_refl h_trans h_total sched_susp h_from
          job_suspension_duration h_arr h_comp h_wc h_resp h_self
          any_j hcw h_cost_incr h_only_j
          (H_positive_costs any_j H_any_j_arrives)
          art h_resp_valid h_resp_tight
          (R (job_task any_j)) h_resp_hc
    _ = R (job_task any_j) - task_cost (job_task any_j) := by rw [hcw_eq]

end JitterOfHigherPriorityJobs

include H_valid_schedule H_jobs_come_from_taskset
  H_valid_response_time_bound_of_hp_tasks_in_all_schedules
  H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
  H_arrival_times_are_consistent H_any_j_arrives H_job_cost_le_task_cost
  H_positive_costs H_job_of_tsk_i in
theorem ts_membership_job_jitter_le_task_jitter :
    job_jitter job_arrival job_task higher_eq_priority job_cost j
      (actual_response_time job_arrival job_task job_cost sched_susp R) any_j ≤
      task_jitter task_cost higher_eq_priority tsk_i R (job_task any_j) := by
  simp only [job_jitter, task_jitter, other_hep_task]
  rw [H_job_of_tsk_i]
  split
  · -- condition true
    rename_i h_cond
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h_cond
    obtain ⟨h_hp, h_diff⟩ := h_cond
    have h_diff' : decide (job_task any_j ≠ tsk_i) = true := by
      simp only [decide_eq_true_eq]; exact h_diff
    have DIFF := ts_membership_difference_in_response_times
      job_arrival job_task ts arr_seq H_arrival_times_are_consistent H_jobs_come_from_taskset
      job_cost task_cost job_suspension_duration higher_eq_priority
      H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
      sched_susp H_valid_schedule tsk_i R H_valid_response_time_bound_of_hp_tasks_in_all_schedules
      H_positive_costs H_job_cost_le_task_cost any_j H_any_j_arrives
      h_hp h_diff'
    exact le_trans (min_le_right _ _) DIFF
  · -- condition false: both are 0
    exact le_refl 0

end JobJitterBoundedByTaskJitter

end ProvingMembership

end TaskSetMembership

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Taskset_membership

end
