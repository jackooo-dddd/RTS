-- Translated from: ../rt-proofs/classic/analysis/uni/susp/dynamic/jitter/rta_by_reduction.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_taskset_generation
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule_service

noncomputable section

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Rta_by_reduction

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule.JitterScheduleConstruction
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_taskset_generation.JitterTaskSetGeneration
open Prosa.Classic.Util.Pick

private abbrev Sched (Job : Type _) [DecidableEq Job] :=
  Prosa.Classic.Model.Schedule.Uni.Schedule.schedule Job

def valid_suspension_aware_schedule
    {Task : Type _} [DecidableEq Task]
    {Job : Type _} [DecidableEq Job]
    (job_arrival : Job → Time)
    (arr_seq : arrival_sequence Job)
    (higher_eq_priority : JLDP_policy Job)
    (job_suspension_duration : job_suspension Job)
    (job_cost : Job → Time)
    (sched_susp : Sched Job) : Prop :=
  Prosa.Classic.Model.Schedule.Uni.Schedule.jobs_come_from_arrival_sequence sched_susp arr_seq ∧
  Prosa.Classic.Model.Schedule.Uni.Schedule.jobs_must_arrive_to_execute job_arrival sched_susp ∧
  Prosa.Classic.Model.Schedule.Uni.Schedule.completed_jobs_dont_execute job_cost sched_susp ∧
  (∀ j t, arrives_in arr_seq j →
    (Prosa.Classic.Model.Schedule.Uni.Schedule.pending job_arrival job_cost sched_susp j t ∧
     ¬ (Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at sched_susp j t = true) ∧
     ¬ suspended_at job_arrival job_cost job_suspension_duration sched_susp j t) →
    ∃ j_other, Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at sched_susp j_other t = true) ∧
  (∀ j j_hp t, arrives_in arr_seq j →
    (Prosa.Classic.Model.Schedule.Uni.Schedule.pending job_arrival job_cost sched_susp j t ∧
     ¬ (Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at sched_susp j t = true) ∧
     ¬ suspended_at job_arrival job_cost job_suspension_duration sched_susp j t) →
    Prosa.Classic.Model.Schedule.Uni.Schedule.scheduled_at sched_susp j_hp t = true →
    higher_eq_priority t j_hp j = true) ∧
  respects_self_suspensions job_arrival job_cost job_suspension_duration sched_susp

namespace RTAByReduction

section ComparingResponseTimeBounds

variable {Task : Type _} [DecidableEq Task]
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

variable (H_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_job_deadlines_equal_task_deadlines :
  ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))

variable (higher_eq_priority : FP_policy Task)
variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
variable (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)

variable (job_cost : Job → Time)
variable (task_cost : Task → Time)

variable (job_suspension_duration : job_suspension Job)
variable (task_suspension_bound : Task → Time)

variable (H_positive_costs :
  ∀ j, arrives_in arr_seq j → job_cost j > 0)

variable (sched_susp : Sched Job)
variable (H_valid_schedule :
  valid_suspension_aware_schedule (Task := Task) job_arrival arr_seq
    (FP_to_JLDP job_task higher_eq_priority)
    job_suspension_duration job_cost sched_susp)

variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

def other_hep_task (tsk_other : Task) : Bool :=
  higher_eq_priority tsk_other tsk && decide (tsk_other ≠ tsk)

variable (R : Task → Time)

variable (H_valid_response_time_bound_of_hp_tasks :
  ∀ tsk_hp,
    tsk_hp ∈ ts →
    other_hep_task higher_eq_priority tsk tsk_hp = true →
    Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime.is_response_time_bound_of_task
      job_arrival job_cost job_task arr_seq sched_susp tsk_hp (R tsk_hp))

def actual_response_time (j_hp : Job) : Time :=
  pick_min (R (job_task j_hp) + 1)
    (fun r => decide (job_cost j_hp ≤ Prosa.Classic.Model.Schedule.Uni.Schedule.service sched_susp j_hp (job_arrival j_hp + r)))

variable (j : Job)
variable (H_j_arrives : arrives_in arr_seq j)
variable (H_job_of_tsk : job_task j = tsk)

variable (H_no_deadline_misses_for_previous_jobs :
  ∀ j0,
    arrives_in arr_seq j0 →
    job_arrival j0 < job_arrival j →
    job_task j0 = job_task j →
    Prosa.Classic.Model.Schedule.Uni.Schedulability.job_misses_no_deadline
      job_arrival job_cost job_deadline sched_susp j0)

variable (H_valid_response_time_bound_in_sched_jitter :
  Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime.is_response_time_bound_of_job
    job_arrival (inflated_job_cost job_cost job_suspension_duration j)
    (sched_jitter job_arrival job_task higher_eq_priority job_cost
      job_suspension_duration arr_seq j
      (actual_response_time job_arrival job_task job_cost sched_susp R))
    j (R tsk))

include job_task arr_seq ts higher_eq_priority job_suspension_duration
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_constrained_deadlines H_sporadic_arrivals H_job_deadlines_equal_task_deadlines
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    H_valid_schedule H_j_arrives task_period task_deadline job_deadline
    H_valid_response_time_bound_of_hp_tasks H_no_deadline_misses_for_previous_jobs
    H_valid_response_time_bound_in_sched_jitter H_job_of_tsk in
theorem valid_response_time_bound_in_sched_susp :
    Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime.is_response_time_bound_of_job
      job_arrival job_cost sched_susp j (R tsk) := by
  -- Construct H_bounded_response_time_of_hp_jobs for jitter_reduction_job_j_completes_no_later
  have H_bounded : ∀ j_hp, arrives_in arr_seq j_hp →
      (higher_eq_priority (job_task j_hp) (job_task j) && decide (job_task j_hp ≠ job_task j)) = true →
      Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime.is_response_time_bound_of_job
        job_arrival job_cost sched_susp j_hp
        (actual_response_time job_arrival job_task job_cost sched_susp R j_hp) := by
    intro j_hp h_arrives h_hep
    unfold actual_response_time
    apply Prosa.Classic.Util.Pick.pick_min_holds
    · -- EX: existence witness
      use R (job_task j_hp)
      constructor
      · exact Nat.lt_succ_of_le le_rfl
      · simp only [decide_eq_true_eq]
        have h_hep' : other_hep_task higher_eq_priority tsk (job_task j_hp) = true := by
          simp only [other_hep_task, Bool.and_eq_true, decide_eq_true_eq]
          rw [H_job_of_tsk] at h_hep
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h_hep
          exact ⟨h_hep.1, h_hep.2⟩
        exact H_valid_response_time_bound_of_hp_tasks (job_task j_hp)
          (H_jobs_from_taskset j_hp h_arrives) h_hep' j_hp h_arrives rfl
    · -- MIN: the minimum satisfies P
      intro r _ h_resp _
      simp only [decide_eq_true_eq] at h_resp
      exact h_resp
  exact @Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Jitter_schedule_service.jitter_reduction_job_j_completes_no_later
    _ _ task_period task_deadline _ _
    job_arrival job_cost job_deadline job_task ts arr_seq
    H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals
    higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total
    job_suspension_duration sched_susp H_valid_schedule
    j H_j_arrives (R tsk) (actual_response_time job_arrival job_task job_cost sched_susp R)
    H_bounded H_no_deadline_misses_for_previous_jobs
    H_valid_response_time_bound_in_sched_jitter

end ComparingResponseTimeBounds

end RTAByReduction

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.Rta_by_reduction

end
