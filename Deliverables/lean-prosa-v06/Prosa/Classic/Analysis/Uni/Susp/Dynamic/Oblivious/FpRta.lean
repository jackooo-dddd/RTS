-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/susp/dynamic/oblivious/fp_rta.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 165)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.ArrivalSequence
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Suspension
import Prosa.Classic.Model.Arrival.Basic.TaskArrival
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals
import Prosa.Classic.Model.Schedule.Uni.Susp.Schedule
import Prosa.Classic.Model.Schedule.Uni.Susp.Platform
import Prosa.Classic.Analysis.Uni.Basic.FpRtaComp
import Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction

/-!
Suspension-oblivious response-time analysis for FP scheduling under the dynamic self-suspension model (Rocq module
`SuspensionObliviousFP` of `classic/analysis/uni/susp/dynamic/oblivious/fp_rta.v`).

Representation notes:
* The section-local `Let`s `inflated_cost`, `task_is_schedulable` and `claimed_to_be_schedulable` are unfolded
  (`inflated_task_cost task_cost task_suspension_bound`, `task_misses_no_deadline …`, `fp_schedulable …`).
* The task set is a `taskset_of SporadicTask` (the accepted `Prosa.Util.Seqset.set`), used as its underlying list
  `ts.val` where the Rocq source coerces it to a sequence. The Rocq module `Export`s `ResponseTimeIterationFP` and
  `ReductionToBasicSchedule`; Lean clients open those namespaces directly.
* The suspension-aware platform predicates (`work_conserving`, `respects_FP_policy`) are those of
  `PlatformWithSuspensions`. The proof is, as in Rocq, the reduction lemma `suspension_oblivious_preserves_schedulability`
  applied to the basic uniprocessor FP RTA (`jobs_schedulable_by_fp_rta`) with the inflated costs.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.FpRta.SuspensionObliviousFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival (sporadic_task_model)
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Suspension.Suspension
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule
open Prosa.Classic.Model.Schedule.Uni.Schedulability.Schedulability (task_misses_no_deadline)
open Prosa.Classic.Model.Schedule.Uni.Susp.SuspensionIntervals.SuspensionIntervals (respects_self_suspensions)
open Prosa.Classic.Analysis.Uni.Basic.FpRtaComp.ResponseTimeIterationFP (fp_schedulable jobs_schedulable_by_fp_rta)
open Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.Reduction.ReductionToBasicSchedule

universe u v

theorem suspension_oblivious_fp_rta_implies_schedulability {SporadicTask : Type u} [DecidableEq SporadicTask]
    (task_cost task_period task_deadline : SporadicTask → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → SporadicTask)
    (ts : taskset_of SporadicTask)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arrival_sequence_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job task_cost task_deadline job_cost job_deadline job_task j)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (higher_eq_priority : FP_policy SporadicTask)
    (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_priority_is_total : FP_is_total_over_task_set higher_eq_priority ts.val)
    (next_suspension : job_suspension Job) (task_suspension_bound : SporadicTask → time)
    (H_dynamic_suspensions : dynamic_suspension_model job_cost job_task next_suspension task_suspension_bound)
    (H_inflated_cost_le_deadline_and_period : ∀ tsk, tsk ∈ ts →
      inflated_task_cost task_cost task_suspension_bound tsk ≤ task_deadline tsk ∧
        inflated_task_cost task_cost task_suspension_bound tsk ≤ task_period tsk)
    (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute job_arrival sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_work_conserving :
      Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions.work_conserving job_arrival job_cost
        next_suspension arr_seq sched)
    (H_respects_priority :
      Prosa.Classic.Model.Schedule.Uni.Susp.Platform.PlatformWithSuspensions.respects_FP_policy job_arrival job_cost
        job_task next_suspension arr_seq sched higher_eq_priority)
    (H_respects_self_suspensions : respects_self_suspensions job_arrival job_cost next_suspension sched)
    (H_claimed_schedulable_by_suspension_oblivious_RTA :
      fp_schedulable (inflated_task_cost task_cost task_suspension_bound) task_period task_deadline higher_eq_priority
        ts.val = true) :
    ∀ tsk, tsk ∈ ts → task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  intro tsk INts j ARRj JOBtsk
  have TRANS : JLDP_is_transitive (FP_to_JLDP job_task higher_eq_priority) :=
    fun t y x z h1 h2 => H_priority_is_transitive _ _ _ h1 h2
  have TOTAL : JLDP_is_total arr_seq (FP_to_JLDP job_task higher_eq_priority) := by
    intro j1 j2 t ARR1 ARR2
    rcases H_priority_is_total _ _ (H_jobs_from_taskset j1 ARR1) (H_jobs_from_taskset j2 ARR2) with h | h
    · simp [FP_to_JLDP, FP_to_JLFP, h]
    · simp [FP_to_JLDP, FP_to_JLFP, h]
  have CONS := H_arrival_times_are_consistent
  exact suspension_oblivious_preserves_schedulability job_arrival job_deadline arr_seq CONS
    (FP_to_JLDP job_task higher_eq_priority) TRANS TOTAL job_cost next_suspension sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_work_conserving
    H_respects_priority H_respects_self_suspensions
    (jobs_schedulable_by_fp_rta (inflated_task_cost task_cost task_suspension_bound) task_period task_deadline
      job_arrival (inflated_job_cost job_cost next_suspension) job_deadline job_task ts
      (suspension_oblivious_task_parameters_remain_valid task_period task_deadline ts.val task_cost
        task_suspension_bound H_inflated_cost_le_deadline_and_period H_valid_task_parameters)
      arr_seq CONS H_arrival_sequence_is_a_set H_jobs_from_taskset
      (suspension_oblivious_job_parameters_remain_valid task_period task_deadline job_deadline job_task ts.val arr_seq
        H_jobs_from_taskset job_cost task_cost next_suspension task_suspension_bound H_dynamic_suspensions
        H_inflated_cost_le_deadline_and_period H_valid_job_parameters)
      H_sporadic_tasks higher_eq_priority H_priority_is_reflexive H_priority_is_transitive
      (sched_new job_arrival arr_seq (FP_to_JLDP job_task higher_eq_priority) job_cost next_suspension sched)
      (sched_newjobs_come_from_arrival_sequence job_arrival arr_seq CONS _ job_cost next_suspension sched
        H_jobs_come_from_arrival_sequence)
      (sched_new_jobs_must_arrive_to_execute job_arrival arr_seq CONS _ job_cost next_suspension sched)
      (sched_new_completed_jobs_dont_execute job_arrival arr_seq CONS _ job_cost next_suspension sched)
      (sched_new_work_conserving job_arrival arr_seq CONS _ job_cost next_suspension sched)
      (sched_new_respects_policy job_arrival arr_seq CONS _ TRANS TOTAL job_cost next_suspension sched)
      H_claimed_schedulable_by_suspension_oblivious_RTA)
    j ARRj

end Prosa.Classic.Analysis.Uni.Susp.Dynamic.Oblivious.FpRta.SuspensionObliviousFP
