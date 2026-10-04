-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/dynamic/jitter/taskset_rta.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 183)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.ValidSchedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.RtaByReduction
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterTasksetGeneration
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.TasksetMembership

/-!
Per-task response-time analysis of suspension-aware task sets via the reduction to jitter-aware task sets (Rocq module
`TaskSetRTA` of `classic/analysis/uni/susp/dynamic/jitter/taskset_rta.v`).

Representation notes:
* The Rocq module aliases are Lean namespace abbreviations of the accepted modules (`ts_gen` is
  `JitterTaskSetGeneration`, `reduction` is `JitterScheduleConstruction`, `reduction_prop` is
  `JitterScheduleProperties`).
* The section-local `Let`s are unfolded: `job_higher_eq_priority` is `FP_to_JLDP job_task higher_eq_priority`;
  `is_valid_suspension_aware_schedule job_cost` and `is_valid_jitter_aware_schedule` are the accepted
  `valid_suspension_aware_schedule …` and `valid_jitter_aware_schedule …` (applied to `FP_to_JLDP job_task
  higher_eq_priority`); `is_task_response_time_bound_with job_cost sched` is `is_response_time_bound_of_task
  job_arrival job_cost job_task arr_seq sched`; `other_hep_task tsk_other` is `higher_eq_priority tsk_other tsk_i &&
  !decide (tsk_other = tsk_i)`; `job_cost_positive`, `job_cost_le_task_cost` and `job_jitter_le_task_jitter` are
  unfolded in `valid_jobs_with_jitter`; `inflated_task_cost` and `task_jitter` are the `ts_gen` definitions applied
  to the section variables.
* Boolean predicates in proposition position are `= true`; `x != y` is `!decide (x = y)`.
* Binder lists follow the Rocq contract. The proof follows the Rocq script: strong induction on the absolute
  response-time bound `job_arrival j + R tsk_i`, the reduction theorem `valid_response_time_bound_in_sched_susp`, and
  the task-set membership lemmas of `TaskSetMembership` (whose `actual_response_time` is definitionally the one of
  `RTAByReduction`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.TasksetRta.TaskSetRTA

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule.ValidSuspensionAwareSchedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.ValidSchedule.ValidJitterAwareSchedule
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.RtaByReduction.RTAByReduction
  (valid_response_time_bound_in_sched_susp)
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.TasksetMembership.TaskSetMembership
  (actual_response_time ts_membership_inflated_job_cost_positive
   ts_membership_inflated_job_cost_le_inflated_task_cost ts_membership_job_jitter_le_task_jitter)
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleProperties.JitterScheduleProperties
  (sched_jitter_is_valid)

namespace ts_gen
export Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterTasksetGeneration.JitterTaskSetGeneration
  (inflated_task_cost task_jitter)
end ts_gen
namespace reduction
export Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule.JitterScheduleConstruction
  (inflated_job_cost job_jitter sched_jitter)
end reduction

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def valid_jobs_with_jitter {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_task : Job → Task) (arr_seq : arrival_sequence Job) (job_cost job_jitter : Job → time)
    (task_cost task_jitter : Task → time) : Prop :=
  (∀ j, arrives_in arr_seq j → 0 < job_cost j) ∧
  (∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j)) ∧
  (∀ j, arrives_in arr_seq j → job_jitter j ≤ task_jitter (job_task j))

theorem valid_response_time_bound_of_tsk_i
    {Task : Type u} [DecidableEq Task]
    (task_cost : Task → time)
    (task_period : Task → time)
    (task_deadline : Task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time)
    (job_deadline : Job → time)
    (job_task : Job → Task)
    (ts : List Task)
    (H_constrained_deadlines : constrained_deadline_model task_period task_deadline ts)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_arrivals : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_jobs_come_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadline_eq_task_deadline :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (job_suspension_duration : job_suspension Job)
    (task_suspension_bound : Task → time)
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)
    (tsk_i : Task)
    (H_tsk_in_ts : tsk_i ∈ ts)
    (R : Task → time)
    (H_valid_response_time_bound_of_hp_tasks_in_all_schedules :
      ∀ (job_cost : Job → time) (sched : schedule Job),
        valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
          job_suspension_duration job_cost sched →
        ∀ tsk_hp, tsk_hp ∈ ts → (higher_eq_priority tsk_hp tsk_i && !decide (tsk_hp = tsk_i)) = true →
          is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk_hp (R tsk_hp))
    (H_R_le_deadline : R tsk_i ≤ task_deadline tsk_i)
    (H_valid_response_time_bound_of_tsk_i :
      ∀ (job_cost job_jitter : Job → time) (sched : schedule Job),
        valid_jobs_with_jitter job_task arr_seq job_cost job_jitter
          (ts_gen.inflated_task_cost task_cost task_suspension_bound tsk_i)
          (ts_gen.task_jitter task_cost higher_eq_priority tsk_i R) →
        valid_jitter_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_cost job_jitter
          sched →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk_i (R tsk_i))
    (job_cost : Job → time)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (H_job_cost_positive : ∀ j, arrives_in arr_seq j → 0 < job_cost j)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))
    (H_dynamic_suspensions :
      dynamic_suspension_model job_cost job_task job_suspension_duration task_suspension_bound) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched_susp tsk_i (R tsk_i) := by
  suffices MAIN : ∀ (n : Nat) (j : Job), job_arrival j + R tsk_i = n → arrives_in arr_seq j → job_task j = tsk_i →
      is_response_time_bound_of_job job_arrival job_cost sched_susp j (R tsk_i) = true by
    intro j ARRj JOBtsk
    exact MAIN _ j rfl ARRj JOBtsk
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro j hn ARRj JOBtsk
    have BEFOREok : ∀ j0, arrives_in arr_seq j0 → job_task j0 = tsk_i → job_arrival j0 < job_arrival j →
        completed_by job_cost sched_susp j0 (job_arrival j0 + R tsk_i) = true :=
      fun j0 ARR0 JOB0 LT0 => IH _ (by omega') j0 rfl ARR0 JOB0
    apply valid_response_time_bound_in_sched_susp task_period task_deadline job_arrival job_deadline job_task ts
      H_constrained_deadlines arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_sporadic_arrivals
      H_jobs_come_from_taskset H_job_deadline_eq_task_deadline higher_eq_priority H_priority_is_reflexive
      H_priority_is_transitive H_priority_is_total job_cost job_suspension_duration sched_susp H_valid_schedule tsk_i R
      (fun tsk_hp IN OHEP => H_valid_response_time_bound_of_hp_tasks_in_all_schedules job_cost sched_susp
        H_valid_schedule tsk_hp IN OHEP) j ARRj JOBtsk
    · intro j0 ARR0 LT0 JOB0
      unfold job_misses_no_deadline
      apply completion_monotonic job_cost sched_susp j0 (job_arrival j0 + R tsk_i)
      · rw [H_job_deadline_eq_task_deadline j0 ARR0, JOB0, JOBtsk]
        omega'
      · exact BEFOREok j0 ARR0 (JOB0.trans JOBtsk) LT0
    · have VALID : valid_jobs_with_jitter job_task arr_seq
          (reduction.inflated_job_cost job_cost job_suspension_duration j)
          (reduction.job_jitter job_arrival job_task higher_eq_priority job_cost j
            (actual_response_time job_arrival job_task job_cost sched_susp R))
          (ts_gen.inflated_task_cost task_cost task_suspension_bound tsk_i)
          (ts_gen.task_jitter task_cost higher_eq_priority tsk_i R) :=
        ⟨ts_membership_inflated_job_cost_positive arr_seq job_cost job_suspension_duration j H_job_cost_positive,
          ts_membership_inflated_job_cost_le_inflated_task_cost job_arrival job_task ts arr_seq job_cost task_cost
            job_suspension_duration task_suspension_bound higher_eq_priority tsk_i H_tsk_in_ts j JOBtsk R
            H_valid_response_time_bound_of_hp_tasks_in_all_schedules H_job_cost_le_task_cost H_dynamic_suspensions,
          fun j' ARR' => ts_membership_job_jitter_le_task_jitter job_arrival job_task ts arr_seq
            H_arrival_times_are_consistent H_jobs_come_from_taskset job_cost task_cost job_suspension_duration
            higher_eq_priority H_priority_is_reflexive H_priority_is_transitive H_priority_is_total sched_susp
            H_valid_schedule tsk_i j JOBtsk R H_valid_response_time_bound_of_hp_tasks_in_all_schedules
            H_job_cost_positive H_job_cost_le_task_cost j' ARR'⟩
      exact H_valid_response_time_bound_of_tsk_i _ _ _ VALID
        (sched_jitter_is_valid job_arrival job_task ts arr_seq H_arrival_times_are_consistent
          H_jobs_come_from_taskset higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
          H_priority_is_total job_cost job_suspension_duration sched_susp H_valid_schedule j ARRj _) j ARRj JOBtsk

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.TasksetRta.TaskSetRTA
