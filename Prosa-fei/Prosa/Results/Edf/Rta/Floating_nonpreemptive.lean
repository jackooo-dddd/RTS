-- Translated from: ../rt-proofs/results/edf/rta/floating_nonpreemptive.v
import Prosa.Results.Edf.Rta.Bounded_nps
import Prosa.Analysis.Facts.Preemption.Rtc_threshold.Floating
import Prosa.Model.Priority.Edf
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic
import Prosa.Model.Preemption.Limited_preemptive
import Prosa.Model.Task.Preemption.Floating_nonpreemptive

namespace Prosa.Results.Edf.Rta.Floating_nonpreemptive

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
open Prosa.Model.Preemption.Limited_preemptive
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.Floating_nonpreemptive
open Prosa.Model.Aggregate.Workload
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.Work_conserving
open Prosa.Model.Schedule.Limited_preemptive
open Prosa.Model.Schedule.Priority_driven
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Request_bound_function
open Prosa.Analysis.Definitions.Priority_inversion
open Prosa.Analysis.Facts.Preemption.Rtc_threshold.Floating
open Prosa.Results.Edf.Rta.Bounded_nps
open Prosa.Results.Edf.Rta.Bounded_pi
open Prosa.Util.Epsilon
open Prosa.Util.Minmax

section RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves

variable {Task : TaskType}
variable [TaskCost Task]
variable [TaskDeadline Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

variable [DecidableEq Task]

attribute [local instance] pstate_instance
attribute [local instance] basic_ready_instance
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JobDeadline Job := job_deadline_from_task_deadline Job Task
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLFP_policy Job := EDF Job
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLDP_policy Job := JLFP_to_JLDP Job

variable (arr_seq : arrival_sequence Job)
variable (H_arrival_times_are_consistent : consistent_arrival_times arr_seq)
variable (H_arr_seq_is_a_set : arrival_sequence_uniq arr_seq)

variable [JobPreemptionPoints Job]
variable [TaskMaxNonpreemptiveSegment Task]
variable (H_valid_task_model_with_floating_nonpreemptive_regions :
  valid_model_with_floating_nonpreemptive_regions (Task := Task) arr_seq)

variable (ts : List Task)

variable (H_all_jobs_from_taskset : all_jobs_from_taskset arr_seq ts)

variable (H_valid_job_cost : arrivals_have_valid_job_costs (Task := Task) arr_seq)

variable [MaxArrivals Task]
variable (H_valid_arrival_curve : valid_taskset_arrival_curve ts max_arrivals)
variable (H_is_arrival_curve : taskset_respects_max_arrivals arr_seq ts)

variable (tsk : Task)
variable (H_tsk_in_ts : tsk ∈ ts)

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence (Job := Job) sched arr_seq)
variable (H_schedule_with_limited_preemptions :
  schedule_respects_preemption_model arr_seq sched)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable (H_sequential_tasks : sequential_tasks (Job := Job) (Task := Task) sched)

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_respects_policy : respects_policy_at_preemption_point arr_seq sched)

noncomputable def blocking_bound (tsk : Task) (ts : List Task) : Nat :=
  bigMaxListCond ts
    (fun tsk_other => decide (tsk_other ≠ tsk) && decide (task_deadline tsk < task_deadline tsk_other))
    (fun tsk_other => task_max_nonpreemptive_segment tsk_other - ε)

variable (L : duration)
variable (H_L_positive : L > 0)
variable (H_fixed_point : L = total_request_bound_function ts L)

variable (R : duration)
variable (H_R_is_maximum :
  ∀ (A : duration),
    is_in_search_space_edf tsk ts L A = true →
    ∃ (F : duration),
      A + F = blocking_bound tsk ts
              + task_request_bound_function tsk (A + ε)
              + bound_on_total_hep_workload tsk ts A (A + F) ∧
      F ≤ R)

attribute [local instance] Prosa.Model.Task.Preemption.Floating_nonpreemptive.fully_preemptive

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_valid_task_model_with_floating_nonpreemptive_regions
  H_all_jobs_from_taskset H_valid_job_cost
  H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts
  H_jobs_come_from_arrival_sequence H_schedule_with_limited_preemptions
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_sequential_tasks H_work_conserving H_respects_policy
  H_L_positive H_fixed_point H_R_is_maximum in
theorem uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions :
    task_response_time_bound arr_seq sched tsk R := by
  have HBNPS := Prosa.Analysis.Facts.Preemption.Task.Floating.floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions
    arr_seq sched H_schedule_with_limited_preemptions H_completed_jobs_dont_execute
    H_valid_task_model_with_floating_nonpreemptive_regions
  have HRTC := floating_preemptive_valid_task_run_to_completion_threshold arr_seq
    H_valid_job_cost tsk
  apply Bounded_nps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set sched
    H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
    H_completed_jobs_dont_execute
    HBNPS
    H_sequential_tasks H_work_conserving H_respects_policy
    ts H_all_jobs_from_taskset H_valid_job_cost
    H_valid_arrival_curve H_is_arrival_curve tsk H_tsk_in_ts
    HBNPS.1
    HRTC
    L H_L_positive H_fixed_point R
  intro A hA
  obtain ⟨F, hEQ, hLE⟩ := H_R_is_maximum A hA
  have HBLOCK : blocking_bound tsk ts = Bounded_nps.blocking_bound tsk ts := by
    unfold blocking_bound Bounded_nps.blocking_bound
    congr 1
    funext x
    simp [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨F, ?_, ?_⟩
  · simp only [task_run_to_completion_threshold, Nat.sub_self, Nat.sub_zero]
    rw [← HBLOCK]; exact hEQ
  · simp only [task_run_to_completion_threshold, Nat.sub_self, Nat.add_zero]; exact hLE

end RTAforModelWithFloatingNonpreemptiveRegionsWithArrivalCurves

end Prosa.Results.Edf.Rta.Floating_nonpreemptive
