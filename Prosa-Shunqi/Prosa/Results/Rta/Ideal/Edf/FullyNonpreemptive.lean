-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/edf/fully_nonpreemptive.v

import Prosa.Results.Rta.Ideal.Edf.BoundedNps
import Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive
import Prosa.Analysis.Facts.Readiness.Basic

namespace Prosa.Results.Rta.Ideal.Edf.FullyNonpreemptive

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
open Prosa.Model.Task.Preemption.FullyNonpreemptive
open Prosa.Model.Preemption.FullyNonpreemptive
open Prosa.Model.Schedule.Nonpreemptive
open Prosa.Analysis.Facts.Preemption.Job.Nonpreemptive
open Prosa.Analysis.Facts.Preemption.Task.Nonpreemptive
open Prosa.Analysis.Facts.Preemption.RtcThreshold.Nonpreemptive

/-! RTA for fully nonpreemptive EDF scheduling on ideal uniprocessors.

Binders follow the elaborated source type. The section's readiness (the accepted `basic_ready_instance`), the EDF
policy (the accepted `EDF` over `job_deadline_from_task_deadline`) and the section-local `fully_nonpreemptive_job_model` (with `fully_nonpreemptive_task_model` and `fully_nonpreemptive_rtc_threshold` used by the proof) are passed
explicitly where the elaborated statement uses them implicitly; the blocking bound at the fully nonpreemptive task model is the accepted `bigMaxListCond`, as in the elaborated statement. The section-local `rbf`, `task_rbf`, `total_rbf` and the
blocking bound are inlined; `bounded_nps.is_in_search_space` is the accepted
`Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space`, `edf.blocking_bound` the accepted EDF blocking bound and
`edf_athep_bound.bound_on_athep_workload` the accepted EDF athep bound. Representation: a Boolean in `Prop` position is
`= true`; `x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`. -/

theorem uniprocessor_response_time_bound_fully_nonpreemptive_edf {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskDeadline Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
    [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals → taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      nonpreemptive_schedule sched →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) fully_nonpreemptive_job_model basic_ready_instance arr_seq sched
        (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
    ∀ L : duration, 0 < L → L = total_request_bound_function ts L →
    ∀ R : Nat,
      (∀ A : duration, Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space ts tsk L A = true →
        ∃ F : Nat,
          bigMaxListCond ts
                (fun tsk_o => blocking_relevant tsk_o && decide (task_deadline tsk + A < task_deadline tsk_o))
                (fun tsk_o => task_cost tsk_o - 1) +
              (task_request_bound_function tsk (A + 1) - (task_cost tsk - 1)) +
              bound_on_athep_workload ts tsk A (A + F) ≤ A + F ∧
            F + (task_cost tsk - 1) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva ts hall hvjc _ hvalid hresp tsk hin sched hvs hnps hwc hrespE L hL hfix R hR
  rcases Nat.eq_zero_or_pos (task_cost tsk) with h0 | hcpos
  · intro j hj htsk
    have hv := hvjc j hj
    unfold valid_job_cost at hv
    rw [of_decide_eq_true htsk, h0] at hv
    have hz : job_cost j = 0 := Nat.le_zero.mp (of_decide_eq_true hv)
    unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [hz]; exact Nat.zero_le _
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JobPreemptable Job := fully_nonpreemptive_job_model
  let _ : TaskRunToCompletionThreshold Task := fully_nonpreemptive_rtc_threshold
  let _ : TaskMaxNonpreemptiveSegment Task := fully_nonpreemptive_task_model
  have hcde := valid_schedule_implies_completed_jobs_dont_execute sched arr_seq hvs
  have hvm : valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched :=
    ⟨valid_fully_nonpreemptive_model arr_seq (ideal_proc_model_provides_unit_service Job) sched hnps hcde,
      fully_nonpreemptive_model_is_model_with_bounded_nonpreemptive_regions arr_seq hvjc⟩
  refine Prosa.Results.Rta.Ideal.Edf.BoundedNps.uniprocessor_response_time_bound_edf_with_bounded_nonpreemptive_segments
    arr_seq hva sched hvs hvm hwc hrespE ts hall hvjc hvalid hresp tsk hin hvm.1 (fully_nonpreemptive_valid_task_run_to_completion_threshold arr_seq tsk hcpos) L hL hfix R ?_
  intro A hA
  exact hR A hA

end Prosa.Results.Rta.Ideal.Edf.FullyNonpreemptive
