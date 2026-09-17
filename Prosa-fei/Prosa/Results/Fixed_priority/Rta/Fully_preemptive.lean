-- Translated from: ../rt-proofs/results/fixed_priority/rta/fully_preemptive.v
import Prosa.Results.Fixed_priority.Rta.Bounded_nps
import Prosa.Analysis.Facts.Preemption.Task.Preemptive
import Prosa.Analysis.Facts.Preemption.Rtc_threshold.Preemptive
import Prosa.Model.Processor.Ideal
import Prosa.Model.Readiness.Basic
import Prosa.Model.Task.Preemption.Fully_preemptive

namespace Prosa.Results.Fixed_priority.Rta.Fully_preemptive

open Prosa.Behavior.Job
open Prosa.Behavior.Time
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Ready
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Processor.Ideal
open Prosa.Model.Priority.Classes
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.Fully_preemptive
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Schedule.Work_conserving
open Prosa.Model.Schedule.Priority_driven
open Prosa.Analysis.Definitions.Priority_inversion
open Prosa.Analysis.Definitions.Job_properties
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.Request_bound_function
open Prosa.Analysis.Facts.Preemption.Task.Preemptive
open Prosa.Analysis.Facts.Preemption.Rtc_threshold.Preemptive
open Prosa.Results.Fixed_priority.Rta.Bounded_nps
open Prosa.Util.Epsilon
open Prosa.Util.Minmax

section RTAforFullyPreemptiveFPModelwithArrivalCurves

variable {Task : TaskType}
variable [TaskCost Task]
variable [DecidableEq Task]

variable {Job : JobType}
variable [DecidableEq Job]
variable [JobTask Job Task]
variable [JobArrival Job]
variable [JobCost Job]

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

attribute [local instance] pstate_instance
attribute [local instance] fully_preemptive_model
attribute [local instance] fully_preemptive

variable (sched : schedule (processor_state Job))
variable (H_jobs_come_from_arrival_sequence :
  jobs_come_from_arrival_sequence (Job := Job) sched arr_seq)

variable (H_jobs_must_arrive_to_execute : jobs_must_arrive_to_execute (Job := Job) sched)
variable (H_completed_jobs_dont_execute : completed_jobs_dont_execute (Job := Job) sched)

variable [FP_policy Task]

set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLFP_policy Job := FP_to_JLFP Job Task
set_option synthInstance.checkSynthOrder false in
noncomputable local instance : JLDP_policy Job := JLFP_to_JLDP Job

variable (H_priority_is_reflexive : reflexive_priorities (Job := Job))
variable (H_priority_is_transitive : transitive_priorities (Job := Job))

variable (H_sequential_tasks : sequential_tasks (Job := Job) (Task := Task) sched)

variable (H_work_conserving : work_conserving arr_seq sched)

variable (H_respects_policy : respects_policy_at_preemption_point arr_seq sched)

noncomputable abbrev rbf := @task_request_bound_function Task _ _

noncomputable abbrev task_rbf := task_request_bound_function tsk

noncomputable abbrev total_hep_rbf := total_hep_request_bound_function_FP ts tsk

noncomputable abbrev total_ohep_rbf := total_ohep_request_bound_function_FP ts tsk

variable (L : duration)
variable (H_L_positive : L > 0)
variable (H_fixed_point : L = total_hep_request_bound_function_FP ts tsk L)

noncomputable abbrev is_in_search_space (A : duration) : Bool :=
  (A < L) && (task_request_bound_function tsk A != task_request_bound_function tsk (A + ε))

variable (R : duration)
variable (H_R_is_maximum :
  ∀ (A : duration),
    is_in_search_space tsk L A = true →
    ∃ (F : duration),
      A + F = task_request_bound_function tsk (A + ε) +
              total_ohep_request_bound_function_FP ts tsk (A + F) ∧
      F ≤ R)

noncomputable abbrev response_time_bounded_by :=
  task_response_time_bound (Task := Task) arr_seq sched

include H_arrival_times_are_consistent H_arr_seq_is_a_set
  H_all_jobs_from_taskset H_valid_job_cost
  H_valid_arrival_curve H_is_arrival_curve
  H_tsk_in_ts
  H_jobs_come_from_arrival_sequence
  H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
  H_priority_is_reflexive H_priority_is_transitive
  H_sequential_tasks H_work_conserving H_respects_policy
  H_L_positive H_fixed_point H_R_is_maximum in
theorem uniprocessor_response_time_bound_fully_preemptive_fp :
    task_response_time_bound arr_seq sched tsk R := by
  have foldl_max_zero : ∀ n, List.foldl max 0 (List.replicate n 0) = 0 := by
    intro n; induction n with
    | zero => simp
    | succ n ih => simp [List.replicate_succ, List.foldl_cons]; exact ih
  have BLOCK : blocking_bound ts tsk = 0 := by
    unfold blocking_bound bigMaxListCond
    simp only [task_max_nonpreemptive_segment, ε, Nat.sub_self]
    simp only [List.map_const']
    exact foldl_max_zero _
  have RTC : task_run_to_completion_threshold tsk = task_cost tsk := by
    simp [task_run_to_completion_threshold]
  have VALID := fully_preemptive_model_is_valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched
  have VALID_RTC := fully_preemptive_valid_task_run_to_completion_threshold arr_seq H_valid_job_cost tsk
  exact uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments
    arr_seq H_arrival_times_are_consistent H_arr_seq_is_a_set
    sched H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
    VALID
    H_priority_is_reflexive H_priority_is_transitive
    H_sequential_tasks H_work_conserving H_respects_policy
    ts H_all_jobs_from_taskset H_valid_job_cost
    H_valid_arrival_curve H_is_arrival_curve
    tsk H_tsk_in_ts
    VALID.1
    VALID_RTC
    L H_L_positive
    (by rw [BLOCK, Nat.zero_add]; exact H_fixed_point)
    R
    (fun A hA => by
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hA
      obtain ⟨hLT, hNEQ⟩ := hA
      have hA' : is_in_search_space tsk L A = true := by
        unfold is_in_search_space
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hLT, hNEQ⟩
      obtain ⟨F, hFIX, hBOUND⟩ := H_R_is_maximum A hA'
      exact ⟨F,
        by simp only [BLOCK, RTC, Nat.zero_add, Nat.sub_self, Nat.sub_zero]; exact hFIX,
        by simp only [RTC, Nat.sub_self, Nat.add_zero]; exact hBOUND⟩)

end RTAforFullyPreemptiveFPModelwithArrivalCurves

end Prosa.Results.Fixed_priority.Rta.Fully_preemptive
