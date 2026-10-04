-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/uni/jitter/fp_rta_theory.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 113)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Arrival.Jitter.TaskArrival
import Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence
import Prosa.Classic.Model.Arrival.Jitter.ArrivalBounds
import Prosa.Classic.Model.Schedule.Uni.ScheduleOfTask
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Schedulability
import Prosa.Classic.Model.Schedule.Uni.ResponseTime
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.BusyInterval
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Analysis.Uni.Jitter.WorkloadBoundFp

/-!
Response-time analysis for jitter-aware uniprocessor FP scheduling (Rocq module `ResponseTimeAnalysisFP` of
`classic/analysis/uni/jitter/fp_rta_theory.v`).

Representation notes: the section-local `Let`s (`response_time_bounded_by`, `W`) are unfolded; `tsk \in ts` is
`tsk ∈ ts`. Binder lists follow the Rocq contract (`task_deadline` and `H_tsk_in_ts` are not taken).
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Uni.Jitter.FpRtaTheory.ResponseTimeAnalysisFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival (sporadic_task_model)
open Prosa.Classic.Model.Arrival.Jitter.ArrivalSequence.ArrivalSequenceWithJitter
open Prosa.Classic.Model.Schedule.Uni.Schedule.UniprocessorSchedule hiding pending backlogged scheduled_implies_pending
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule.UniprocessorScheduleWithJitter
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
open Prosa.Classic.Model.Schedule.Uni.ResponseTime.ResponseTime
open Prosa.Classic.Analysis.Uni.Jitter.WorkloadBoundFp.WorkloadBoundFP

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

theorem uniprocessor_response_time_bound_fp {SporadicTask : Type u} [DecidableEq SporadicTask]
    (task_cost task_period task_jitter : SporadicTask → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_jitter : Job → time) (job_task : Job → SporadicTask) (ts : List SporadicTask)
    (H_positive_periods : ∀ tsk, tsk ∈ ts → 0 < task_period tsk) (arr_seq : arrival_sequence Job)
    (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
    (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (H_job_cost_le_task_cost : ∀ j, arrives_in arr_seq j → job_cost j ≤ task_cost (job_task j))
    (H_job_jitter_le_task_jitter : ∀ j, arrives_in arr_seq j → job_jitter j ≤ task_jitter (job_task j))
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts) (sched : schedule Job)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (higher_eq_priority : FP_policy SporadicTask) (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
    (H_priority_is_transitive : FP_is_transitive higher_eq_priority)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_fp_policy : respects_FP_policy job_arrival job_cost job_jitter job_task arr_seq sched higher_eq_priority)
    (tsk : SporadicTask) (R : time) (H_R_positive : 0 < R)
    (H_response_time_is_fixed_point :
      R = total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk R) :
    is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
  intro j IN JOBtsk
  have JIT := H_job_jitter_le_task_jitter j IN
  rw [JOBtsk] at JIT
  have BOUND := Prosa.Classic.Model.Schedule.Uni.Jitter.BusyInterval.BusyInterval.busy_interval_bounds_response_time
    job_arrival job_cost job_jitter arr_seq H_arrival_times_are_consistent sched H_jobs_come_from_arrival_sequence
    (FP_to_JLFP job_task higher_eq_priority) j IN H_arr_seq_is_a_set H_jobs_execute_after_jitter
    H_completed_jobs_dont_execute H_work_conserving H_respects_fp_policy
    (fun x => H_priority_is_reflexive (job_task x))
    (fun y x z => H_priority_is_transitive (job_task y) (job_task x) (job_task z)) R H_R_positive
    (fun t => by
      have := fp_workload_bound_holds task_cost task_period task_jitter job_arrival job_cost job_jitter job_task ts
        H_positive_periods arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set H_all_jobs_from_taskset
        H_job_cost_le_task_cost H_job_jitter_le_task_jitter H_sporadic_tasks tsk higher_eq_priority R
        H_response_time_is_fixed_point t
      unfold Prosa.Classic.Model.Schedule.Uni.Workload.Workload.workload_of_higher_or_equal_priority_tasks at this
      unfold Prosa.Classic.Model.Schedule.Uni.Workload.Workload.workload_of_higher_or_equal_priority_jobs FP_to_JLFP
      rw [JOBtsk]
      exact this)
  unfold is_response_time_bound_of_job
  apply completion_monotonic job_cost sched j _ _ _ BOUND
  unfold actual_arrival
  omega'

end Prosa.Classic.Analysis.Uni.Jitter.FpRtaTheory.ResponseTimeAnalysisFP
