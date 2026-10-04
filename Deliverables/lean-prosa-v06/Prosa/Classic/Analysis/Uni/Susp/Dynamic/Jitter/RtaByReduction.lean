-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/dynamic/jitter/rta_by_reduction.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 175)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Workload
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.ValidSchedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleProperties
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleService
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterTasksetGeneration

/-!
Task response-time bounds in suspension-aware schedules via the reduction to jitter-aware schedules (Rocq module
`RTAByReduction` of `classic/analysis/uni/susp/dynamic/jitter/rta_by_reduction.v`).

Representation notes:
* The Rocq module aliases are Lean namespace abbreviations of the accepted modules (`reduction` is
  `JitterScheduleConstruction`, `reduction_serv` is `JitterScheduleService`).
* `[pick-min r <= N | P r]` is the accepted classic `Prosa.Classic.Util.Pick.pick_min (N + 1) (fun r => P r)`, as in
  the accepted `taskset_membership.v` translation.
* The section-local `Let`s are unfolded: `job_higher_eq_priority` is `FP_to_JLDP job_task higher_eq_priority`;
  `other_hep_task tsk_other` is `higher_eq_priority tsk_other tsk && !decide (tsk_other = tsk)`;
  `task_response_time_in_sched_susp_bounded_by`, `job_response_time_in_sched_susp_bounded_by` and
  `job_response_time_in_sched_jitter_bounded_by` are the accepted `is_response_time_bound_of_task`/`_of_job`;
  `job_misses_no_deadline_in_sched_susp` is `job_misses_no_deadline … sched_susp`; `sched_jitter`,
  `inflated_job_cost` and `job_jitter` are the `reduction` definitions instantiated with `actual_response_time`.
  The unused `Let`s `inflated_task_cost`/`task_jitter` (and the section variables `task_cost`,
  `task_suspension_bound`, `H_positive_costs` they mention) do not occur in any statement, as in the Rocq contract.
* Boolean predicates in proposition position are `= true`; `x != y` is `!decide (x = y)`.
* Binder lists follow the Rocq contract. The proof is, as in Rocq, an application of
  `jitter_reduction_job_j_completes_no_later`.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.RtaByReduction.RTAByReduction

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
open Prosa.Classic.Util.Pick (pick_min pick_min_holds)

namespace reduction
export Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterSchedule.JitterScheduleConstruction
  (inflated_job_cost job_jitter sched_jitter)
end reduction
namespace reduction_serv
export Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.JitterScheduleService.JitterScheduleService
  (jitter_reduction_job_j_completes_no_later)
end reduction_serv

universe u v

def actual_response_time {Task : Type u} [DecidableEq Task] {Job : Type v} [DecidableEq Job]
    (job_arrival : Job → time) (job_task : Job → Task) (job_cost : Job → time) (sched_susp : schedule Job)
    (R : Task → time) (j_hp : Job) : time :=
  pick_min (R (job_task j_hp) + 1) (fun r => is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp r)

theorem valid_response_time_bound_in_sched_susp
    {Task : Type u} [DecidableEq Task]
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
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_job_deadlines_equal_task_deadlines :
      ∀ j, arrives_in arr_seq j → job_deadline j = task_deadline (job_task j))
    (higher_eq_priority : FP_policy Task)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts)
    (job_cost : Job → time)
    (job_suspension_duration : job_suspension Job)
    (sched_susp : schedule Job)
    (H_valid_schedule :
      valid_suspension_aware_schedule job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority)
        job_suspension_duration job_cost sched_susp)
    (tsk : Task)
    (R : Task → time)
    (H_valid_response_time_bound_of_hp_tasks :
      ∀ tsk_hp, tsk_hp ∈ ts → (higher_eq_priority tsk_hp tsk && !decide (tsk_hp = tsk)) = true →
        is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched_susp tsk_hp (R tsk_hp))
    (j : Job)
    (H_j_arrives : arrives_in arr_seq j)
    (H_job_of_tsk : job_task j = tsk)
    (H_no_deadline_misses_for_previous_jobs :
      ∀ j0, arrives_in arr_seq j0 → job_arrival j0 < job_arrival j → job_task j0 = job_task j →
        job_misses_no_deadline job_arrival job_cost job_deadline sched_susp j0)
    (H_valid_response_time_bound_in_sched_jitter :
      is_response_time_bound_of_job job_arrival (reduction.inflated_job_cost job_cost job_suspension_duration j)
        (reduction.sched_jitter job_arrival job_task arr_seq higher_eq_priority job_cost job_suspension_duration j
          (actual_response_time job_arrival job_task job_cost sched_susp R)) j (R tsk) = true) :
    is_response_time_bound_of_job job_arrival job_cost sched_susp j (R tsk) = true := by
  apply reduction_serv.jitter_reduction_job_j_completes_no_later task_period task_deadline job_arrival job_cost
    job_deadline job_task ts arr_seq H_arrival_times_are_consistent H_arrival_sequence_is_a_set H_jobs_from_taskset
    H_job_deadlines_equal_task_deadlines H_constrained_deadlines H_sporadic_arrivals higher_eq_priority
    H_priority_is_reflexive H_priority_is_transitive H_priority_is_total job_suspension_duration sched_susp
    H_valid_schedule j H_j_arrives (R tsk) (actual_response_time job_arrival job_task job_cost sched_susp R) _
    H_no_deadline_misses_for_previous_jobs H_valid_response_time_bound_in_sched_jitter
  intro j_hp ARRhp OTHERhp
  unfold actual_response_time
  apply pick_min_holds _ _ (fun x => is_response_time_bound_of_job job_arrival job_cost sched_susp j_hp x = true)
  · refine ⟨R (job_task j_hp), Nat.lt_succ_self _, ?_⟩
    apply H_valid_response_time_bound_of_hp_tasks (job_task j_hp) (H_jobs_from_taskset j_hp ARRhp)
      (by rw [← H_job_of_tsk]; exact OTHERhp) j_hp ARRhp rfl
  · intro x _ hx _
    exact hx

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Jitter.RtaByReduction.RTAByReduction
