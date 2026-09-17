-- Translated from: ../rt-proofs/classic/analysis/uni/jitter/fp_rta_theory.v
import Prosa.Classic.Util.All
import Prosa.Classic.Model.Priority
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Jitter.Job
import Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
import Prosa.Classic.Model.Arrival.Basic.Task_arrival
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Classic.Model.Schedule.Uni.Schedule_of_task
import Prosa.Classic.Model.Schedule.Uni.Service
import Prosa.Classic.Model.Schedule.Uni.Response_time
import Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
import Prosa.Classic.Model.Schedule.Uni.Jitter.Platform
import Prosa.Classic.Analysis.Uni.Jitter.Workload_bound_fp
import Prosa.Classic.Model.Schedule.Uni.Jitter.Busy_interval

namespace Prosa.Classic.Analysis.Uni.Jitter.Fp_rta_theory

open Prosa.Classic.Model.Time
open Prosa.Classic.Model.Arrival.Basic.Arrival_sequence
open Prosa.Classic.Model.Arrival.Basic.Task_arrival
open Prosa.Classic.Model.Arrival.Jitter.Arrival_sequence
open Prosa.Classic.Model.Schedule.Uni.Schedule
open Prosa.Classic.Model.Schedule.Uni.Response_time.ResponseTime
open Prosa.Classic.Model.Schedule.Uni.Jitter.Schedule
open Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform
open Prosa.Classic.Model.Priority
open Prosa.Classic.Analysis.Uni.Jitter.Workload_bound_fp.WorkloadBoundFP

namespace ResponseTimeAnalysisFP

section ResponseTimeBound

  variable {SporadicTask : Type _} [DecidableEq SporadicTask]
  variable (task_cost : SporadicTask → Time)
  variable (task_period : SporadicTask → Time)
  variable (task_deadline : SporadicTask → Time)
  variable (task_jitter : SporadicTask → Time)

  variable {Job : Type _} [DecidableEq Job]
  variable (job_arrival : Job → Time)
  variable (job_cost : Job → Time)
  variable (job_jitter : Job → Time)
  variable (job_task : Job → SporadicTask)

  variable (ts : List SporadicTask)

  variable (H_positive_periods : ∀ tsk, tsk ∈ ts → task_period tsk > 0)

  variable (arr_seq : arrival_sequence Job)
  variable (H_arrival_times_are_consistent : arrival_times_are_consistent job_arrival arr_seq)
  variable (H_arr_seq_is_a_set : arrival_sequence_is_a_set arr_seq)

  variable (H_sporadic_tasks :
    sporadic_task_model task_period job_arrival job_task arr_seq)

  variable (H_job_cost_le_task_cost :
    ∀ j,
      arrives_in arr_seq j →
      job_cost j ≤ task_cost (job_task j))

  variable (H_job_jitter_le_task_jitter :
    ∀ j,
      arrives_in arr_seq j →
      job_jitter j ≤ task_jitter (job_task j))

  variable (H_all_jobs_from_taskset :
    ∀ j, arrives_in arr_seq j → job_task j ∈ ts)

  variable (sched : schedule Job)
  variable (H_jobs_come_from_arrival_sequence :
    jobs_come_from_arrival_sequence sched arr_seq)

  variable (H_jobs_execute_after_jitter :
    jobs_execute_after_jitter job_arrival job_jitter sched)
  variable (H_completed_jobs_dont_execute :
    completed_jobs_dont_execute job_cost sched)

  variable (higher_eq_priority : FP_policy SporadicTask)
  variable (H_priority_is_reflexive : FP_is_reflexive higher_eq_priority)
  variable (H_priority_is_transitive : FP_is_transitive higher_eq_priority)

  variable (H_work_conserving :
    Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform.work_conserving
      job_arrival job_cost job_jitter arr_seq sched)
  variable (H_respects_fp_policy :
    Prosa.Classic.Model.Schedule.Uni.Jitter.Platform.Platform.respects_FP_policy
      job_arrival job_cost job_jitter job_task arr_seq sched higher_eq_priority)

  variable (tsk : SporadicTask)
  variable (H_tsk_in_ts : tsk ∈ ts)

  variable (R : Time)
  variable (H_R_positive : R > 0)
  variable (H_response_time_is_fixed_point :
    R = total_workload_bound_fp task_cost task_period task_jitter higher_eq_priority ts tsk R)

  include H_positive_periods H_arrival_times_are_consistent H_arr_seq_is_a_set
          H_sporadic_tasks H_job_cost_le_task_cost H_job_jitter_le_task_jitter
          H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence
          H_jobs_execute_after_jitter H_completed_jobs_dont_execute
          H_priority_is_reflexive H_priority_is_transitive
          H_work_conserving H_respects_fp_policy
          H_tsk_in_ts H_R_positive H_response_time_is_fixed_point

  include H_positive_periods H_arrival_times_are_consistent H_arr_seq_is_a_set H_sporadic_tasks H_job_cost_le_task_cost H_job_jitter_le_task_jitter H_all_jobs_from_taskset H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_priority_is_reflexive H_priority_is_transitive H_work_conserving H_respects_fp_policy H_tsk_in_ts H_R_positive H_response_time_is_fixed_point in
  theorem uniprocessor_response_time_bound_fp :
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched
        tsk (task_jitter tsk + R) := by
    intro j IN JOBtsk
    unfold is_response_time_bound_of_job
    apply completion_monotonic job_cost sched j (actual_arrival job_arrival job_jitter j + R)
    · -- actual_arrival j + R ≤ job_arrival j + (task_jitter tsk + R)
      have haa : actual_arrival job_arrival job_jitter j = job_arrival j + job_jitter j := rfl
      have hjle := H_job_jitter_le_task_jitter j IN
      rw [JOBtsk] at hjle
      simp only [Time] at *
      omega
    · -- completed_by ... j (actual_arrival j + R)
      have h_workload : ∀ t,
          Prosa.Classic.Model.Schedule.Uni.Workload.workload_of_higher_or_equal_priority_jobs
            job_cost
            (actual_arrivals_between job_arrival job_jitter arr_seq t (t + R))
            (FP_to_JLFP job_task higher_eq_priority) j ≤ R := by
        intro t
        have hwb := fp_workload_bound_holds task_cost task_period task_jitter job_arrival job_cost
          job_jitter job_task ts H_positive_periods arr_seq H_arrival_times_are_consistent
          H_arr_seq_is_a_set H_all_jobs_from_taskset H_job_cost_le_task_cost
          H_job_jitter_le_task_jitter H_sporadic_tasks tsk H_tsk_in_ts
          higher_eq_priority R H_response_time_is_fixed_point t
        convert hwb using 1
        simp only [Prosa.Classic.Model.Schedule.Uni.Workload.workload_of_higher_or_equal_priority_tasks,
                    Prosa.Classic.Model.Schedule.Uni.Workload.workload_of_higher_or_equal_priority_jobs,
                    FP_to_JLFP, JOBtsk]
      exact Prosa.Classic.Model.Schedule.Uni.Jitter.Busy_interval.BusyInterval.busy_interval_bounds_response_time
        job_arrival job_cost job_jitter
        arr_seq H_arrival_times_are_consistent
        sched H_jobs_come_from_arrival_sequence
        (FP_to_JLFP job_task higher_eq_priority)
        j IN
        H_arr_seq_is_a_set H_jobs_execute_after_jitter H_completed_jobs_dont_execute
        H_work_conserving H_respects_fp_policy
        (fun x => H_priority_is_reflexive (job_task x))
        (fun x y z h1 h2 => H_priority_is_transitive (job_task x) (job_task y) (job_task z) h1 h2)
        R H_R_positive h_workload

end ResponseTimeBound

end ResponseTimeAnalysisFP

end Prosa.Classic.Analysis.Uni.Jitter.Fp_rta_theory
