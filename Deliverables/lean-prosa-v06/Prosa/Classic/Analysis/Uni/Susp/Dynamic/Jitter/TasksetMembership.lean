-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/dynamic/jitter/taskset_membership.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 150)

import Prosa.Classic.Util.All
import Prosa.Classic.Util.Pick
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterTasksetGeneration
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction
import Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.ReductionProperties

/-!
The jitter-aware schedule of the reduction is an instance of the generated jitter-aware task set (Rocq module
`TaskSetMembership` of `classic/analysis/uni/susp/dynamic/jitter/taskset_membership.v`).

Representation notes:
* The Rocq module aliases (`reduction`, `ts_gen`, `sust`, `sust_prop`, `valid_sched`, `job_susp`, `job_jitter`) are
  Lean namespace abbreviations of the accepted modules.
* `[pick-min r <= N | P r]` is the accepted classic `Prosa.Classic.Util.Pick.pick_min (N + 1) (fun r => P r)`.
* `x != y` in proposition position is `(!decide (x = y)) = true`; Boolean predicates in proposition position are
  `= true`.
* The section-local `Let`s (`job_higher_eq_priority`, `is_valid_suspension_aware_schedule`,
  `task_response_time_in_sched_susp_bounded_by`, `job_response_time_in_sched_susp_bounded_by`,
  `is_task_response_time_bound_with`, `other_hep_task`, `inflated_job_cost`, `job_jitter`, `inflated_task_cost`,
  `task_jitter`, `higher_cost_wcet`, `sched_susp_highercost`,
  `task_response_time_in_sched_susp_highercost_bounded_by`) are unfolded; `other_hep_task tsk` is
  `higher_eq_priority tsk tsk_i && !decide (tsk = tsk_i)` and `higher_cost_wcet` is
  `fun j' => if j' = any_j then task_cost (job_task any_j) else job_cost j'`.
* Binder lists follow the Rocq contract.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.TasksetMembership.TaskSetMembership

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule.ValidSuspensionAwareSchedule
open Prosa.Classic.Util.Pick (pick_min pick_min_holds pick_min_ltn)

namespace reduction
export Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule.JitterScheduleConstruction
  (inflated_job_cost job_jitter)
end reduction
namespace ts_gen
export Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterTasksetGeneration.JitterTaskSetGeneration
  (inflated_task_cost task_jitter)
end ts_gen
namespace sust
export Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.Reduction.SustainabilitySingleCost
  (sched_susp_highercost)
end sust
namespace sust_prop
export Prosa.Classic.Analysis.Uni.Susp.Sustainability.Singlecost.ReductionProperties.SustainabilitySingleCostProperties
  (sched_susp_highercost_jobs_come_from_arrival_sequence sched_susp_highercost_jobs_must_arrive_to_execute
   sched_susp_highercost_completed_jobs_dont_execute sched_susp_highercost_work_conserving
   sched_susp_highercost_respects_policy sched_susp_highercost_respects_self_suspensions
   sched_susp_highercost_incurs_more_interference)
end sust_prop

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

/-! ### Actual response times of higher-priority jobs -/

def actual_response_time {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (job_cost : Job → time)
    (sched_susp : schedule Job) (R : Task → time) (j_hp : Job) : time :=
  pick_min (R (job_task j_hp) + 1) (fun r => is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp r)

theorem actual_response_time_is_valid {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job) (H_jobs_come_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (higher_eq_priority : FP_policy Task)
    (sched_susp : schedule Job) (H_valid_schedule : valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched_susp) (tsk_i : Task) (R : Task → time)
    (H_valid_response_time_bound_of_hp_tasks_in_all_schedules :
      ∀ (job_cost : Job → time) (sched : schedule Job),
        valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched →
        ∀ tsk_hp, tsk_hp ∈ ts → (higher_eq_priority tsk_hp tsk_i && !decide (tsk_hp = tsk_i)) = true →
          is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk_hp (R tsk_hp)) :
    ∀ j_hp, arrives_in arr_seq j_hp → (higher_eq_priority (job_task j_hp) tsk_i && !decide ((job_task j_hp) = tsk_i)) = true →
      is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp (actual_response_time job_arrival job_task job_cost sched_susp R j_hp) = true := by
  intro j_hp ARRhp HP
  unfold actual_response_time
  apply pick_min_holds _ _ (fun x => is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp x = true)
  · exact ⟨R (job_task j_hp), Nat.lt_succ_self _,
      H_valid_response_time_bound_of_hp_tasks_in_all_schedules job_cost sched_susp H_valid_schedule (job_task j_hp)
        (H_jobs_come_from_taskset j_hp ARRhp) HP j_hp ARRhp rfl⟩
  · intro x _ hx _; exact hx

theorem actual_response_time_is_minimum {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job) (H_jobs_come_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (higher_eq_priority : FP_policy Task)
    (sched_susp : schedule Job) (H_valid_schedule : valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched_susp) (tsk_i : Task) (R : Task → time)
    (H_valid_response_time_bound_of_hp_tasks_in_all_schedules :
      ∀ (job_cost : Job → time) (sched : schedule Job),
        valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched →
        ∀ tsk_hp, tsk_hp ∈ ts → (higher_eq_priority tsk_hp tsk_i && !decide (tsk_hp = tsk_i)) = true →
          is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk_hp (R tsk_hp)) :
    ∀ j_hp r_hp, arrives_in arr_seq j_hp → (higher_eq_priority (job_task j_hp) tsk_i && !decide ((job_task j_hp) = tsk_i)) = true →
      is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp r_hp = true →
      actual_response_time job_arrival job_task job_cost sched_susp R j_hp ≤ r_hp := by
  intro j_hp r_hp ARRhp HP RESP
  have EX : ∃ x, x < R (job_task j_hp) + 1 ∧
      is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp x = true :=
    ⟨R (job_task j_hp), Nat.lt_succ_self _,
      H_valid_response_time_bound_of_hp_tasks_in_all_schedules job_cost sched_susp H_valid_schedule (job_task j_hp)
        (H_jobs_come_from_taskset j_hp ARRhp) HP j_hp ARRhp rfl⟩
  unfold actual_response_time
  rcases Nat.lt_or_ge r_hp (R (job_task j_hp) + 1) with LT | GE
  · exact pick_min_holds _ _ (fun x => x ≤ r_hp) EX (fun x _ _ MIN => MIN r_hp LT RESP)
  · exact Nat.le_of_lt (Nat.lt_of_lt_of_le (pick_min_ltn _ _ EX) GE)

/-! ### Task set membership -/

theorem ts_membership_inflated_job_cost_positive {Job : Type v} [DecidableEq Job] (arr_seq : arrival_sequence Job)
    (job_cost : Job → time) (job_suspension_duration : job_suspension Job) (j : Job)
    (H_positive_costs : ∀ j, arrives_in arr_seq j → 0 < job_cost j) :
    ∀ j0, arrives_in arr_seq j0 → 0 < reduction.inflated_job_cost job_cost job_suspension_duration j j0 := by
  intro j0 ARR0
  have := H_positive_costs j0 ARR0
  unfold reduction.inflated_job_cost
  split <;> omega'

theorem ts_membership_inflated_job_cost_le_inflated_task_cost {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job)
    (job_cost : Job → time) (task_cost : Task → time) (job_suspension_duration : job_suspension Job)
    (task_suspension_bound : Task → time) (higher_eq_priority : FP_policy Task) (tsk_i : Task)
    (H_tsk_in_ts : tsk_i ∈ ts) (j : Job) (H_job_of_tsk_i : job_task j = tsk_i) (R : Task → time)
    (H_valid_response_time_bound_of_hp_tasks_in_all_schedules :
      ∀ (job_cost : Job → time) (sched : schedule Job),
        valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched →
        ∀ tsk_hp, tsk_hp ∈ ts → (higher_eq_priority tsk_hp tsk_i && !decide (tsk_hp = tsk_i)) = true →
          is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk_hp (R tsk_hp))
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))
    (H_dynamic_suspensions :
      dynamic_suspension_model job_cost job_task job_suspension_duration task_suspension_bound) :
    ∀ j', arrives_in arr_seq j' →
      reduction.inflated_job_cost job_cost job_suspension_duration j j' ≤
        ts_gen.inflated_task_cost task_cost task_suspension_bound tsk_i (job_task j') := by
  intro j' ARR'
  have LE := H_job_cost_le_task_cost j' ARR'
  unfold reduction.inflated_job_cost ts_gen.inflated_task_cost
  by_cases EQ : j' = j
  · subst EQ
    have DYN := H_dynamic_suspensions j'
    simp only [if_true, H_job_of_tsk_i] at LE DYN ⊢
    omega'
  · simp only [EQ, if_false]
    split <;> omega'

theorem response_time_bound_in_sched_susp_highercost {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (H_jobs_come_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (job_cost : Job → time) (task_cost : Task → time) (job_suspension_duration : job_suspension Job)
    (higher_eq_priority : FP_policy Task) (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts) (sched_susp : schedule Job)
    (H_valid_schedule : valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched_susp) (tsk_i : Task) (R : Task → time)
    (H_valid_response_time_bound_of_hp_tasks_in_all_schedules :
      ∀ (job_cost : Job → time) (sched : schedule Job),
        valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched →
        ∀ tsk_hp, tsk_hp ∈ ts → (higher_eq_priority tsk_hp tsk_i && !decide (tsk_hp = tsk_i)) = true →
          is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk_hp (R tsk_hp))
    (any_j : Job) :
    ∀ tsk_hp, tsk_hp ∈ ts → (higher_eq_priority tsk_hp tsk_i && !decide (tsk_hp = tsk_i)) = true →
      is_response_time_bound_of_task job_arrival (fun j' => if j' = any_j then task_cost (job_task any_j) else job_cost j') job_task arr_seq (sust.sched_susp_highercost job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) sched_susp job_suspension_duration (fun j' => if j' = any_j then task_cost (job_task any_j) else job_cost j')) tsk_hp (R tsk_hp) := by
  obtain ⟨FROMs, MUST, COMPL, WORK, PRIO, SELF⟩ := H_valid_schedule
  apply H_valid_response_time_bound_of_hp_tasks_in_all_schedules
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact sust_prop.sched_susp_highercost_jobs_come_from_arrival_sequence job_arrival arr_seq
      H_arrival_times_are_consistent (FP_to_JLDP job_task higher_eq_priority) sched_susp FROMs job_suspension_duration MUST _
  · exact sust_prop.sched_susp_highercost_jobs_must_arrive_to_execute job_arrival arr_seq
      H_arrival_times_are_consistent (FP_to_JLDP job_task higher_eq_priority) sched_susp job_suspension_duration MUST _
  · exact sust_prop.sched_susp_highercost_completed_jobs_dont_execute job_arrival arr_seq
      H_arrival_times_are_consistent (FP_to_JLDP job_task higher_eq_priority) sched_susp job_suspension_duration MUST _
  · exact sust_prop.sched_susp_highercost_work_conserving job_arrival arr_seq
      H_arrival_times_are_consistent (FP_to_JLDP job_task higher_eq_priority) sched_susp job_suspension_duration MUST _
  · exact sust_prop.sched_susp_highercost_respects_policy job_arrival arr_seq H_arrival_times_are_consistent
      (FP_to_JLDP job_task higher_eq_priority) (fun t y x z h1 h2 => H_priority_is_transitive (job_task y) (job_task x) (job_task z) h1 h2)
      (fun j1 j2 t ARR1 ARR2 => by
        rcases H_priority_is_total (job_task j1) (job_task j2) (H_jobs_come_from_taskset j1 ARR1)
          (H_jobs_come_from_taskset j2 ARR2) with h | h
        · simp [FP_to_JLDP, FP_to_JLFP, h]
        · simp [FP_to_JLDP, FP_to_JLFP, h])
      sched_susp job_suspension_duration MUST _
  · exact sust_prop.sched_susp_highercost_respects_self_suspensions job_arrival arr_seq
      H_arrival_times_are_consistent (FP_to_JLDP job_task higher_eq_priority) sched_susp job_suspension_duration MUST _

theorem ts_membership_difference_in_response_times {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (H_jobs_come_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (job_cost : Job → time) (task_cost : Task → time) (job_suspension_duration : job_suspension Job)
    (higher_eq_priority : FP_policy Task) (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts) (sched_susp : schedule Job)
    (H_valid_schedule : valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched_susp) (tsk_i : Task) (R : Task → time)
    (H_valid_response_time_bound_of_hp_tasks_in_all_schedules :
      ∀ (job_cost : Job → time) (sched : schedule Job),
        valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched →
        ∀ tsk_hp, tsk_hp ∈ ts → (higher_eq_priority tsk_hp tsk_i && !decide (tsk_hp = tsk_i)) = true →
          is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk_hp (R tsk_hp))
    (H_positive_costs : ∀ j, arrives_in arr_seq j → 0 < job_cost j)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))
    (any_j : Job) (H_any_j_arrives : arrives_in arr_seq any_j)
    (H_higher_priority : higher_eq_priority (job_task any_j) tsk_i = true)
    (H_different_task : (!decide (job_task any_j = tsk_i)) = true) :
    actual_response_time job_arrival job_task job_cost sched_susp R any_j - job_cost any_j ≤ R (job_task any_j) - task_cost (job_task any_j) := by
  have HPany : (higher_eq_priority (job_task any_j) tsk_i && !decide ((job_task any_j) = tsk_i)) = true := by
    simp only [H_higher_priority, H_different_task, Bool.and_self]
  have VALIDr := actual_response_time_is_valid job_arrival job_task ts arr_seq H_jobs_come_from_taskset job_cost
    job_suspension_duration higher_eq_priority sched_susp H_valid_schedule tsk_i R
    H_valid_response_time_bound_of_hp_tasks_in_all_schedules any_j H_any_j_arrives HPany
  have MINr := actual_response_time_is_minimum job_arrival job_task ts arr_seq H_jobs_come_from_taskset job_cost
    job_suspension_duration higher_eq_priority sched_susp H_valid_schedule tsk_i R
    H_valid_response_time_bound_of_hp_tasks_in_all_schedules any_j
  have RESPhp := response_time_bound_in_sched_susp_highercost job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_come_from_taskset job_cost task_cost job_suspension_duration
    higher_eq_priority H_priority_is_transitive H_priority_is_total sched_susp H_valid_schedule tsk_i R
    H_valid_response_time_bound_of_hp_tasks_in_all_schedules any_j (job_task any_j)
    (H_jobs_come_from_taskset any_j H_any_j_arrives) HPany any_j H_any_j_arrives rfl
  obtain ⟨FROMs, MUST, COMPL, WORK, PRIO, SELF⟩ := H_valid_schedule
  have MORE := sust_prop.sched_susp_highercost_incurs_more_interference job_arrival job_cost arr_seq
    H_arrival_times_are_consistent (FP_to_JLDP job_task higher_eq_priority) (fun t x => H_priority_is_reflexive (job_task x)) sched_susp FROMs
    job_suspension_duration MUST COMPL WORK PRIO SELF any_j (fun j' => if j' = any_j then task_cost (job_task any_j) else job_cost j')
    (by simp only [if_true]; exact H_job_cost_le_task_cost any_j H_any_j_arrives)
    (fun x NEQ => by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NEQ
      simp [NEQ])
    (H_positive_costs any_j H_any_j_arrives) (actual_response_time job_arrival job_task job_cost sched_susp R any_j) VALIDr
    (fun r' RESP => MINr r' H_any_j_arrives HPany RESP) (R (job_task any_j)) RESPhp
  simpa using MORE

theorem ts_membership_job_jitter_le_task_jitter {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job] (job_arrival : Job → time) (job_task : Job → Task) (ts : List Task) (arr_seq : arrival_sequence Job) (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq) (H_jobs_come_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (job_cost : Job → time) (task_cost : Task → time) (job_suspension_duration : job_suspension Job)
    (higher_eq_priority : FP_policy Task) (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts) (sched_susp : schedule Job)
    (H_valid_schedule : valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched_susp) (tsk_i : Task) (j : Job) (H_job_of_tsk_i : job_task j = tsk_i) (R : Task → time)
    (H_valid_response_time_bound_of_hp_tasks_in_all_schedules :
      ∀ (job_cost : Job → time) (sched : schedule Job),
        valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_suspension_duration job_cost sched →
        ∀ tsk_hp, tsk_hp ∈ ts → (higher_eq_priority tsk_hp tsk_i && !decide (tsk_hp = tsk_i)) = true →
          is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk_hp (R tsk_hp))
    (H_positive_costs : ∀ j, arrives_in arr_seq j → 0 < job_cost j)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))
    (any_j : Job) (H_any_j_arrives : arrives_in arr_seq any_j) :
    reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j (actual_response_time job_arrival job_task job_cost sched_susp R) any_j ≤
      ts_gen.task_jitter task_cost higher_eq_priority tsk_i R (job_task any_j) := by
  unfold reduction.job_jitter ts_gen.task_jitter
  rw [H_job_of_tsk_i]
  split
  · next COND =>
    simp only [Bool.and_eq_true] at COND
    have DIFF := ts_membership_difference_in_response_times job_arrival job_task ts arr_seq
      H_arrival_times_are_consistent H_jobs_come_from_taskset job_cost task_cost job_suspension_duration
      higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total sched_susp
      H_valid_schedule tsk_i R H_valid_response_time_bound_of_hp_tasks_in_all_schedules H_positive_costs
      H_job_cost_le_task_cost any_j H_any_j_arrives COND.1 COND.2
    exact Nat.le_trans (Nat.min_le_right _ _) DIFF
  · exact Nat.zero_le _

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.TasksetMembership.TaskSetMembership
