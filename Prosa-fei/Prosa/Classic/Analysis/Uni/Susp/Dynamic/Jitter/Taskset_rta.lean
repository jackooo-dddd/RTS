-- Translated from: ../rt-proofs/classic/analysis/uni/susp/dynamic/jitter/taskset_rta.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Valid_schedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Rta_by_reduction
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Taskset_membership

noncomputable section

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Taskset_rta

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Jitter.Valid_schedule.ValidJitterAwareSchedule
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Rta_by_reduction
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Rta_by_reduction.RTAByReduction
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_taskset_generation.JitterTaskSetGeneration
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule.JitterScheduleConstruction

namespace TaskSetRTA

section PerTaskAnalysis

variable {Task : Type _} [DecidableEq Task]
variable (task_cost : Task → Time)
variable (task_period : Task → Time)
variable (task_deadline : Task → Time)
variable {Job : Type _} [DecidableEq Job]
variable (job_arrival : Job → Time)
variable (job_deadline : Job → Time)
variable (job_task : Job → Task)

variable (ts : List Task)
variable (H_constrained_deadlines :
  constrained_deadline_model task_period task_deadline ts)

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent :
  arrival_times_are_consistent job_arrival arr_seq)
variable (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)

variable (H_sporadic_arrivals :
  sporadic_task_model task_period job_arrival job_task arr_seq)

variable (H_jobs_come_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_job_deadline_eq_task_deadline :
  ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))

variable (job_suspension_duration : job_suspension Job)
variable (task_suspension_bound : Task → Time)

variable (higher_eq_priority : FP_policy Task)
variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
variable (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)

variable (tsk_i : Task)
variable (H_tsk_in_ts : tsk_i ∈ ts)

variable (R : Task → Time)

variable (H_valid_response_time_bound_of_hp_tasks_in_all_schedules :
  ∀ job_cost sched,
    valid_suspension_aware_schedule (Task := Task) job_arrival arr_seq
      (FP_to_JLDP job_task higher_eq_priority)
      job_suspension_duration job_cost sched →
    ∀ tsk_hp,
      tsk_hp ∈ ts →
      (higher_eq_priority tsk_hp tsk_i && decide (tsk_hp ≠ tsk_i)) = true →
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk_hp (R tsk_hp))

variable (H_R_le_deadline : R tsk_i ≤ task_deadline tsk_i)

def valid_jobs_with_jitter
    (job_cost : Job → Time)
    (job_jitter : Job → Time)
    (inflated_task_cost : Task → Time)
    (task_jitter : Task → Time) : Prop :=
  (∀ j, arrives_in arr_seq j → job_cost j > 0) ∧
  (∀ j, arrives_in arr_seq j → job_cost j ≤ inflated_task_cost (job_task j)) ∧
  (∀ j, arrives_in arr_seq j → job_jitter j ≤ task_jitter (job_task j))

variable (H_valid_response_time_bound_of_tsk_i :
  ∀ job_cost' job_jitter sched,
    valid_jobs_with_jitter job_task arr_seq job_cost' job_jitter
      (inflated_task_cost task_cost task_suspension_bound tsk_i)
      (task_jitter task_cost higher_eq_priority tsk_i R) →
    valid_jitter_aware_schedule job_arrival arr_seq
      (FP_to_JLDP job_task higher_eq_priority) job_cost' job_jitter sched →
    is_response_time_bound_of_task job_arrival job_cost' job_task arr_seq sched tsk_i (R tsk_i))

variable (job_cost : Job → Time)

variable (sched_susp : schedule Job)
variable (H_valid_schedule :
  valid_suspension_aware_schedule (Task := Task) job_arrival arr_seq
    (FP_to_JLDP job_task higher_eq_priority)
    job_suspension_duration job_cost sched_susp)

variable (H_job_cost_positive :
  ∀ j, arrives_in arr_seq j → job_cost j > 0)

variable (H_job_cost_le_task_cost :
  ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))

variable (H_dynamic_suspensions :
  dynamic_suspension_model job_cost job_task job_suspension_duration task_suspension_bound)

include ts H_constrained_deadlines H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    H_sporadic_arrivals H_jobs_come_from_taskset H_job_deadline_eq_task_deadline
    job_suspension_duration task_suspension_bound task_cost
    higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    H_valid_response_time_bound_of_hp_tasks_in_all_schedules H_R_le_deadline
    H_valid_response_time_bound_of_tsk_i H_valid_schedule
    H_job_cost_positive H_job_cost_le_task_cost H_dynamic_suspensions
    task_period task_deadline job_deadline in
theorem valid_response_time_bound_of_tsk_i :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched_susp tsk_i (R tsk_i) := by
  intro j ARRj JOBtsk
  have key : ∀ (n : Nat), (∀ m, m < n → ∀ j', arrives_in arr_seq j' → job_task j' = tsk_i →
    job_arrival j' + R tsk_i = m → completed_by job_cost sched_susp j' (job_arrival j' + R tsk_i)) →
    ∀ j', arrives_in arr_seq j' → job_task j' = tsk_i →
    job_arrival j' + R tsk_i = n → completed_by job_cost sched_susp j' (job_arrival j' + R tsk_i) := by
    intro n IH j' ARRj' JOBtsk' EQn
    -- 1. Construct H_hp_resp (response time bounds for hep tasks)
    have H_hp_resp : ∀ tsk_hp ∈ ts,
        RTAByReduction.other_hep_task higher_eq_priority tsk_i tsk_hp = true →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched_susp
          tsk_hp (R tsk_hp) :=
      fun tsk_hp h_in h_ohep =>
        H_valid_response_time_bound_of_hp_tasks_in_all_schedules job_cost sched_susp
          H_valid_schedule tsk_hp h_in h_ohep
    -- 2. Construct H_no_miss (no deadline misses for earlier jobs of same task)
    have H_no_miss : ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j' →
        job_task j0 = job_task j' →
        Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline
          job_arrival job_cost job_deadline sched_susp j0 := by
      intro j0 h_arr h_lt h_task
      unfold Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline
      have h_before : job_arrival j0 + R tsk_i < n := by
        rw [← EQn]; exact Nat.add_lt_add_right h_lt (R tsk_i)
      have h_comp := IH (job_arrival j0 + R tsk_i) h_before j0 h_arr (h_task.trans JOBtsk') rfl
      have h_le : job_arrival j0 + R tsk_i ≤ job_arrival j0 + job_deadline j0 := by
        rw [H_job_deadline_eq_task_deadline j0 h_arr, h_task, JOBtsk']
        exact Nat.add_le_add_left H_R_le_deadline _
      -- Bridge Schedule.completed_by → Schedulability.job_misses_no_deadline
      simp only [Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline,
        Prosa.Classic.Model.Schedule.Uni.Schedulability.completed_by,
        Prosa.Classic.Model.Schedule.Uni.Schedulability.service,
        Prosa.Classic.Model.Schedule.Uni.Schedulability.service_during]
      simp only [completed_by, service, service_during] at h_comp
      have sa_eq : ∀ t', service_at sched_susp j0 t' =
          Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at sched_susp j0 t' := by
        intro t'
        simp only [service_at, scheduled_at,
          Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at,
          Prosa.Classic.Model.Schedule.Uni.Schedulability.scheduled_at]
        have : ∀ (b : Bool), b.toNat = if b = true then 1 else 0 := by
          intro b; cases b <;> rfl
        exact this _
      have h_eq : ∑ t ∈ Finset.Ico 0 (job_arrival j0 + R tsk_i),
          service_at sched_susp j0 t =
          ∑ t ∈ Finset.Ico 0 (job_arrival j0 + R tsk_i),
          Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at sched_susp j0 t :=
        Finset.sum_congr rfl (fun t _ => sa_eq t)
      have h_mono : ∑ t ∈ Finset.Ico 0 (job_arrival j0 + R tsk_i),
          Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at sched_susp j0 t ≤
          ∑ t ∈ Finset.Ico 0 (job_arrival j0 + job_deadline j0),
          Prosa.Classic.Model.Schedule.Uni.Schedulability.service_at sched_susp j0 t :=
        Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico_right h_le)
      exact le_trans (le_trans h_comp (le_of_eq h_eq)) h_mono
    -- 3. Construct H_jitter_resp (response time bound in jitter schedule)
    open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Taskset_membership.TaskSetMembership in
    open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule_properties.JitterScheduleProperties in
    set R_hp := RTAByReduction.actual_response_time job_arrival job_task job_cost sched_susp R with R_hp_def
    have H_valid_jobs : valid_jobs_with_jitter job_task arr_seq
        (inflated_job_cost job_cost job_suspension_duration j')
        (job_jitter job_arrival job_task higher_eq_priority job_cost j' R_hp)
        (inflated_task_cost task_cost task_suspension_bound tsk_i)
        (task_jitter task_cost higher_eq_priority tsk_i R) := by
      refine ⟨?_, ?_, ?_⟩
      · exact fun j_x h_arr => ts_membership_inflated_job_cost_positive arr_seq job_cost
          job_suspension_duration j' H_job_cost_positive j_x h_arr
      · exact fun j_x h_arr => ts_membership_inflated_job_cost_le_inflated_task_cost
          job_task arr_seq job_cost task_cost job_suspension_duration task_suspension_bound
          tsk_i j' ARRj' JOBtsk' H_job_cost_le_task_cost H_dynamic_suspensions j_x h_arr
      · exact fun j_x h_arr => ts_membership_job_jitter_le_task_jitter
          job_arrival job_task ts arr_seq H_arrival_times_are_consistent
          H_jobs_come_from_taskset job_cost task_cost job_suspension_duration higher_eq_priority
          H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
          sched_susp H_valid_schedule tsk_i j' JOBtsk' R
          H_valid_response_time_bound_of_hp_tasks_in_all_schedules
          H_job_cost_positive H_job_cost_le_task_cost j_x h_arr
    have H_valid_sched_j : valid_jitter_aware_schedule job_arrival arr_seq
        (FP_to_JLDP job_task higher_eq_priority)
        (inflated_job_cost job_cost job_suspension_duration j')
        (job_jitter job_arrival job_task higher_eq_priority job_cost j' R_hp)
        (sched_jitter job_arrival job_task higher_eq_priority job_cost
          job_suspension_duration arr_seq j' R_hp) :=
      sched_jitter_is_valid job_arrival job_task ts arr_seq
        H_arrival_times_are_consistent H_jobs_come_from_taskset higher_eq_priority
        H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
        job_cost job_suspension_duration sched_susp
        ⟨H_valid_schedule.1, H_valid_schedule.2.1, H_valid_schedule.2.2.1, trivial⟩
        j' ARRj' R_hp
    have H_jitter_resp := H_valid_response_time_bound_of_tsk_i
      (inflated_job_cost job_cost job_suspension_duration j')
      (job_jitter job_arrival job_task higher_eq_priority job_cost j' R_hp)
      (sched_jitter job_arrival job_task higher_eq_priority job_cost
        job_suspension_duration arr_seq j' R_hp)
      H_valid_jobs H_valid_sched_j j' ARRj' JOBtsk'
    -- 4. Apply the main theorem
    exact @valid_response_time_bound_in_sched_susp _ _ task_period task_deadline _ _
      job_arrival job_deadline job_task ts H_constrained_deadlines arr_seq
      H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_arrivals
      H_jobs_come_from_taskset H_job_deadline_eq_task_deadline higher_eq_priority
      H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
      job_cost job_suspension_duration sched_susp H_valid_schedule
      tsk_i R H_hp_resp j' ARRj' JOBtsk' H_no_miss H_jitter_resp
  exact WellFounded.recursion Nat.lt_wfRel.wf (job_arrival j + R tsk_i) key j ARRj JOBtsk rfl

end PerTaskAnalysis

end TaskSetRTA

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Taskset_rta

end
