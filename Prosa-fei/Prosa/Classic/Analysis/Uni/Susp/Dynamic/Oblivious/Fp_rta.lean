-- Translated from: ../rt-proofs/classic/analysis/uni/susp/dynamic/oblivious/fp_rta.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals
import Prosa.Classic.Analysis.Uni.Basic.Fp_rta_comp
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Mathlib.Tactic

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Fp_rta

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Job
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Priority
open Prosa.Classic.Model.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Schedulability
  hiding schedule scheduled_at service_at service_during service completed_by
    completed_jobs_dont_execute completion_monotonic
open Prosa.Classic.Analysis.Uni.Basic.Fp_rta_comp.ResponseTimeIterationFP
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction.ReductionToBasicSchedule
open Prosa.Classic.Model.Schedule.Uni.Susp.Suspension_intervals

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Classical in
attribute [local instance] propDecidable

noncomputable section

namespace SuspensionObliviousFP

section ReductionToBasicAnalysis

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
variable (H_arrival_times_are_consistent :
  arrival_times_are_consistent job_arrival arr_seq)
variable (H_arrival_sequence_is_a_set :
  arrival_sequence_is_a_set arr_seq)

variable (H_jobs_from_taskset :
  ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

variable (H_valid_job_parameters :
  ∀ j,
    arrives_in arr_seq j →
    valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)

variable (H_sporadic_tasks :
  Prosa.Classic.Model.Arrival.Basic.Task_arrival.sporadic_task_model
    task_period job_arrival job_task arr_seq)

variable (higher_eq_priority : FP_policy SporadicTask)
variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
variable (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)

variable (next_suspension : job_suspension Job)
variable (task_suspension_bound : SporadicTask → Time)
variable (H_dynamic_suspensions :
  dynamic_suspension_model job_cost job_task next_suspension task_suspension_bound)

variable (H_inflated_cost_le_deadline_and_period :
  ∀ tsk,
    tsk ∈ ts →
    inflated_task_cost task_cost task_suspension_bound tsk ≤ task_deadline tsk ∧
    inflated_task_cost task_cost task_suspension_bound tsk ≤ task_period tsk)

section MainProof

variable (sched : schedule Job)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence sched arr_seq)

variable (H_jobs_must_arrive_to_execute :
  jobs_must_arrive_to_execute job_arrival sched)

variable (H_completed_jobs_dont_execute :
  completed_jobs_dont_execute job_cost sched)

variable (H_work_conserving :
  susp_aware.work_conserving job_arrival job_cost next_suspension arr_seq sched)

variable (H_respects_priority :
  susp_aware.respects_JLDP_policy job_arrival job_cost next_suspension arr_seq
    sched (FP_to_JLDP job_task higher_eq_priority))

variable (H_respects_self_suspensions :
  respects_self_suspensions job_arrival job_cost next_suspension sched)

variable (H_claimed_schedulable_by_suspension_oblivious_RTA :
  fp_schedulable (inflated_task_cost task_cost task_suspension_bound)
    task_period task_deadline higher_eq_priority ts)

include H_valid_task_parameters H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks H_priority_is_reflexive H_priority_is_transitive H_priority_is_total H_dynamic_suspensions H_inflated_cost_le_deadline_and_period H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving H_respects_priority H_respects_self_suspensions H_claimed_schedulable_by_suspension_oblivious_RTA in
theorem suspension_oblivious_fp_rta_implies_schedulability :
    ∀ tsk,
      tsk ∈ ts →
      task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  intro tsk h_in j h_arr h_tsk_eq
  -- Build JLDP priority from FP priority
  set jldp := FP_to_JLDP job_task higher_eq_priority with jldp_def
  have h_refl : JLDP_is_reflexive jldp := fun t x => H_priority_is_reflexive (job_task x)
  have h_trans : JLDP_is_transitive jldp :=
    fun t y x z hxy hyz => H_priority_is_transitive (job_task y) (job_task x) (job_task z) hxy hyz
  have h_total : JLDP_is_total arr_seq jldp :=
    fun j1 j2 t h1 h2 => H_priority_is_total (job_task j1) (job_task j2)
      (H_jobs_from_taskset j1 h1) (H_jobs_from_taskset j2 h2)
  -- Set up the generated suspension-oblivious schedule
  set sn := sched_new job_arrival job_cost next_suspension arr_seq jldp sched
  -- Prove properties of sched_new
  have h_sn_from := @sched_new_jobs_come_from_arrival_sequence SporadicTask _ Job _
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset jldp h_refl h_trans h_total
    job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
  have h_sn_arrive := @sched_new_jobs_must_arrive_to_execute SporadicTask _ Job _
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset jldp h_refl h_trans h_total
    job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
  have h_sn_completed := @sched_new_completed_jobs_dont_execute SporadicTask _ Job _
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset jldp h_refl h_trans h_total
    job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
  have h_sn_wc := @sched_new_work_conserving SporadicTask _ Job _
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset jldp h_refl h_trans h_total
    job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
  have h_sn_policy := @sched_new_respects_policy SporadicTask _ Job _
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset jldp h_refl h_trans h_total
    job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
  -- Prove inflated task and job parameters are valid
  have h_task_valid := @suspension_oblivious_task_parameters_remain_valid SporadicTask _
    task_period task_deadline Job _
    job_arrival job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset jldp h_refl h_trans h_total
    job_cost task_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
    H_inflated_cost_le_deadline_and_period H_valid_task_parameters
  have h_job_valid := @suspension_oblivious_job_parameters_remain_valid SporadicTask _
    task_period task_deadline Job _
    job_arrival job_deadline job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset jldp h_refl h_trans h_total
    job_cost task_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions
    H_inflated_cost_le_deadline_and_period H_valid_job_parameters
  -- Prove schedulability in the generated schedule
  have h_sched_new := @jobs_schedulable_by_fp_rta SporadicTask _
    (inflated_task_cost task_cost task_suspension_bound)
    task_period task_deadline Job _
    job_arrival (inflated_job_cost job_cost next_suspension) job_deadline job_task
    ts h_task_valid
    arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set
    H_jobs_from_taskset h_job_valid H_sporadic_tasks
    higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
    sn h_sn_from h_sn_arrive h_sn_completed h_sn_wc h_sn_policy
    H_claimed_schedulable_by_suspension_oblivious_RTA
  -- Apply the main reduction theorem
  exact @suspension_oblivious_preserves_schedulability SporadicTask _ Job _
    job_arrival job_deadline job_task ts arr_seq
    H_arrival_times_are_consistent H_jobs_from_taskset
    jldp h_refl h_trans h_total
    job_cost next_suspension task_suspension_bound H_dynamic_suspensions
    sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute H_work_conserving H_respects_priority
    H_respects_self_suspensions h_sched_new j h_arr

end MainProof

end ReductionToBasicAnalysis

end SuspensionObliviousFP

end

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Fp_rta
