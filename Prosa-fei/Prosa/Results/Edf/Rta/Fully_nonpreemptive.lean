-- Translated from: ../rt-proofs/results/edf/rta/fully_nonpreemptive.v
import Prosa.Results.Edf.Rta.Bounded_nps
import Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
import Prosa.Analysis.Facts.Preemption.Rtc_threshold.Nonpreemptive
import Prosa.Model.Priority.Edf
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic
import Prosa.Model.Task.Preemption.Fully_nonpreemptive

namespace Prosa.Results.Edf.Rta.Fully_nonpreemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Absolute_deadline
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Processor.Ideal
open Prosa.Model.Priority.Classes
open Prosa.Model.Priority.Edf
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Schedule.Work_conserving
open Prosa.Model.Schedule.Priority_driven
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Request_bound_function
open Prosa.Analysis.Definitions.Priority_inversion
open Prosa.Analysis.Facts.Busy_interval.Priority_inversion
open Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
open Prosa.Analysis.Facts.Preemption.Rtc_threshold.Nonpreemptive
open Prosa.Results.Edf.Rta.Bounded_nps
open Prosa.Results.Edf.Rta.Bounded_pi
open Prosa.Util.Epsilon
open Prosa.Util.Minmax

section RTAforFullyNonPreemptiveEDFModelwithArrivalCurves

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskDeadline Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable [DecidableEq Task]

attribute [local instance] Prosa.Model.Task.Preemption.Fully_nonpreemptive.fully_nonpreemptive_model
attribute [local instance] Prosa.Model.Task.Preemption.Fully_nonpreemptive.fully_nonpreemptive
attribute [local instance] pstate_instance
attribute [local instance] Prosa.Model.Readiness.Basic.basic_ready_instance
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JobDeadline Job := job_deadline_from_task_deadline Job Task
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLFP_policy Job := EDF Job
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLDP_policy Job := JLFP_to_JLDP Job

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq)

variable (ts : List Task)

variable (H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts)

variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

variable [MaxArrivals Task]
variable (H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals)
variable (H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts)

variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

variable (sched : schedule (processor_state Job))
variable (H_nonpreemptive_sched : nonpreemptive_schedule (Job := Job) sched)
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence (Job := Job) sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (H_sequential_tasks : sequential_tasks (Job := Job) (Task := Task) sched)

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_respects_policy : respects_policy_at_preemption_point arr_seq sched)

variable (L : duration)
variable (H_L_positive : L > 0)
variable (H_fixed_point : L = total_request_bound_function ts L)

variable (R : duration)
variable (H_R_is_maximum :
  ∀ (A : duration),
    is_in_search_space_edf tsk ts L A = true →
    ∃ (F : duration),
      A + F = blocking_bound tsk ts
              + (task_request_bound_function tsk (A + ε) -
                  (task_cost tsk - ε))
              + bound_on_total_hep_workload tsk ts A (A + F) ∧
      F + (task_cost tsk - ε) ≤ R)

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_jobs_come_from_arrival_sequence H_nonpreemptive_sched
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_all_jobs_from_taskset H_valid_job_cost
  H_sequential_tasks H_work_conserving H_respects_policy
  H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts
  H_L_positive H_fixed_point H_R_is_maximum in
theorem uniprocessor_response_time_bound_fully_nonpreemptive_edf :
    task_response_time_bound arr_seq sched tsk R := by
  rcases Nat.eq_zero_or_pos (task_cost tsk) with hzero | hpos
  · -- Case: task_cost tsk = 0
    intro j harr htsk
    unfold job_response_time_bound completed_by
    have hvalid := H_valid_job_cost j harr
    unfold valid_job_cost at hvalid
    rw [htsk, hzero] at hvalid
    simp at hvalid; simp [hvalid]
  · -- Case: task_cost tsk > 0
    have VALID := fully_nonpreemptive_model_is_valid_model_with_bounded_nonpreemptive_regions
      arr_seq H_arrival_times_are_consistent sched H_nonpreemptive_sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_valid_job_cost
    have VALID_RTC := fully_nonpreemptive_valid_task_run_to_completion_threshold
      arr_seq H_arrival_times_are_consistent sched H_nonpreemptive_sched
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute tsk hpos
    exact uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
      arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
      sched H_jobs_come_from_arrival_sequence
      H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      VALID
      H_sequential_tasks H_work_conserving H_respects_policy
      ts H_all_jobs_from_taskset H_valid_job_cost
      H_valid_arrival_curve H_is_arrival_curve
      tsk H_tsk_in_ts
      VALID.1
      VALID_RTC
      L H_L_positive H_fixed_point R H_R_is_maximum

end RTAforFullyNonPreemptiveEDFModelwithArrivalCurves

end Prosa.Results.Edf.Rta.Fully_nonpreemptive
