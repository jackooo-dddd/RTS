-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/edf/floating_nonpreemptive.v

import Prosa.Results.Rta.Ideal.Edf.BoundedNps
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Floating
import Prosa.Analysis.Facts.Preemption.Task.Floating
import Prosa.Analysis.Facts.Readiness.Basic

namespace Prosa.Results.Rta.Ideal.Edf.FloatingNonpreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Edf
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.Ideal
open Prosa.Util.Minmax
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Edf
open Prosa.Analysis.Definitions.Workload.EdfAthepBound
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Model.Task.Preemption.FloatingNonpreemptive
open Prosa.Model.Preemption.LimitedPreemptive
open Prosa.Model.Schedule.LimitedPreemptive
open Prosa.Analysis.Facts.Preemption.Job.Limited
open Prosa.Analysis.Facts.Preemption.Task.Floating
open Prosa.Analysis.Facts.Preemption.RtcThreshold.Floating

/-! RTA for EDF scheduling with floating nonpreemptive regions on ideal uniprocessors.

Binders follow the elaborated source type. The section's readiness (the accepted `basic_ready_instance`), the EDF
policy (the accepted `EDF` over `job_deadline_from_task_deadline`) and the section-local `limited_preemptive_job_model` (with `floating_preemptive_rtc_threshold` used by the proof) are passed
explicitly where the elaborated statement uses them implicitly. The section-local `rbf`, `task_rbf`, `total_rbf` and the
blocking bound are inlined; `bounded_nps.is_in_search_space` is the accepted
`Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space`, `edf.blocking_bound` the accepted EDF blocking bound and
`edf_athep_bound.bound_on_athep_workload` the accepted EDF athep bound. Representation: a Boolean in `Prop` position is
`= true`; `x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`. -/

theorem uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ [JobPreemptionPoints Job] [TaskMaxNonpreemptiveSegment Task],
      valid_model_with_floating_nonpreemptive_regions (Task := Task) arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals → taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @schedule_respects_preemption_model Job _ (processor_state Job) limited_preemptive_job_model arr_seq sched →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) limited_preemptive_job_model basic_ready_instance arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
    ∀ R : duration,
      (∀ A : duration, Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space ts tsk L A = true →
        ∃ F : duration,
          blocking_bound ts tsk A + task_request_bound_function tsk (A + 1) + bound_on_athep_workload ts tsk A (A + F) ≤
            A + F ∧ F ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva _ _ hfl ts hall hvjc _ hvalid hresp tsk hin sched hvs hrpm hwc hrespE L hL hfix R hR
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JobPreemptable Job := limited_preemptive_job_model
  let _ : TaskRunToCompletionThreshold Task := floating_preemptive_rtc_threshold
  have hvm : valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched :=
    floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions arr_seq sched hrpm hfl
  refine Prosa.Results.Rta.Ideal.Edf.BoundedNps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
    arr_seq hva sched hvs hvm hwc hrespE ts hall hvjc hvalid hresp tsk hin hvm.1 (floating_preemptive_valid_task_run_to_completion_threshold arr_seq hvjc tsk) L hL hfix R ?_
  intro A hA
  obtain ⟨F, hF, hFR⟩ := hR A hA
  refine ⟨F, ?_, ?_⟩
  · show blocking_bound ts tsk A + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_cost tsk)) +
        bound_on_athep_workload ts tsk A (A + F) ≤ A + F
    ((try dsimp only [instant, duration, work] at *) <;> omega)
  · show F + (task_cost tsk - task_cost tsk) ≤ R
    ((try dsimp only [instant, duration, work] at *) <;> omega)

end Prosa.Results.Rta.Ideal.Edf.FloatingNonpreemptive
