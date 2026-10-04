-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/fp/limited_preemptive.v

import Prosa.Results.Rta.Ideal.Fp.BoundedNps
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited
import Prosa.Analysis.Facts.Readiness.Sequential
import Prosa.Model.Task.Preemption.LimitedPreemptive
import Prosa.Analysis.Definitions.BlockingBound.Fp

namespace Prosa.Results.Rta.Ideal.Fp.LimitedPreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.LimitedPreemptive
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.LimitedPreemptive
open Prosa.Model.Schedule.LimitedPreemptive
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Readiness.Sequential
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.Ideal
open Prosa.Util.Minmax
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Fp
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Facts.Readiness.Sequential
open Prosa.Analysis.Facts.Preemption.Job.Limited
open Prosa.Analysis.Facts.Preemption.Task.Limited
open Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited

/-! RTA for FP scheduling with fixed preemption points on ideal uniprocessors.

Binders follow the elaborated source type. The source's section-local instances are passed explicitly where the
elaborated statement uses them implicitly: the accepted `limited_preemptive_job_model` and the accepted
`sequential_ready_instance arr_seq` (the local `sequential_readiness`); `limited_preemptions_rtc_threshold` is used by the
proof. The section-local `rbf`, `task_rbf`, `total_hep_rbf`, `total_ohep_rbf`, `blocking_bound` (the accepted FP
blocking bound, at the task model induced by the task preemption points) and the local search-space abbreviation are inlined; `fp.bounded_pi.is_in_search_space` is the
accepted `Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space`. Representation: a Boolean in `Prop` position is
`= true`; `x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`. -/

theorem uniprocessor_response_time_bound_fp_with_fixed_preemption_points {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [JobPreemptionPoints Job] [TaskPreemptionPoints Task], valid_fixed_preemption_points_model arr_seq ts →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals → taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ (sequential_ready_instance (Task := Task) arr_seq)
        arr_seq →
      @schedule_respects_preemption_model Job _ (processor_state Job) limited_preemptive_job_model arr_seq sched →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job)
        (sequential_ready_instance (Task := Task) arr_seq) arr_seq sched →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ (processor_state Job) limited_preemptive_job_model
        (sequential_ready_instance (Task := Task) arr_seq) arr_seq sched FP →
    ∀ L : duration, 0 < L →
      L = blocking_bound (FP := FP) ts tsk + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ R : Nat,
      (∀ A : duration, Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space tsk L A = true →
        ∃ F : duration,
          blocking_bound (FP := FP) ts tsk + (task_request_bound_function tsk (A + 1) - (task_last_nonpr_segment tsk - 1)) +
              total_ohep_request_bound_function_FP ts (FP := FP) tsk (A + F) ≤ A + F ∧
            F + (task_last_nonpr_segment tsk - 1) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva ts hall hcost _ _ hfpp _ hvalid hresp tsk hin sched hvs hrpm FP hrefl htrans hwc hrespFP L hL hfix R hR
  rcases Nat.eq_zero_or_pos (task_cost tsk) with h0 | hcpos
  · intro j hj htsk
    have hv := hcost j hj
    unfold valid_job_cost at hv
    rw [of_decide_eq_true htsk, h0] at hv
    have hz : job_cost j = 0 := Nat.le_zero.mp (of_decide_eq_true hv)
    unfold job_response_time_bound completed_by
    apply decide_eq_true; rw [hz]; exact Nat.zero_le _
  let _ : JobReady Job (processor_state Job) := sequential_ready_instance (Task := Task) arr_seq
  let _ : JobPreemptable Job := limited_preemptive_job_model
  let _ : TaskRunToCompletionThreshold Task := limited_preemptions_rtc_threshold
  have hwb := sequential_readiness_implies_work_bearing_readiness (Task := Task) arr_seq hva.1 sched FP hrefl
  have hvm : valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched :=
    fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions arr_seq sched hrpm ts hfpp
  have hEq : task_cost tsk - (task_cost tsk - (task_last_nonpr_segment tsk - 1)) = task_last_nonpr_segment tsk - 1 :=
    last_segment_eq_cost_minus_rtct arr_seq ts hfpp tsk hin
  refine Prosa.Results.Rta.Ideal.Fp.BoundedNps.uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments
    hrefl htrans arr_seq hva sched hwb hvs hvm hwc hrespFP
    (sequential_readiness_implies_sequential_tasks arr_seq hva.1 sched hvs) ts hall hcost hvalid hresp tsk hin hvm.1
    (limited_valid_task_run_to_completion_threshold arr_seq sched hrpm ts hfpp tsk hin hcpos) L hL hfix R ?_
  intro A hA
  obtain ⟨F, hF, hFR⟩ := hR A hA
  refine ⟨F, ?_, ?_⟩
  · show blocking_bound (FP := FP) ts tsk +
        (task_request_bound_function tsk (A + 1) - (task_cost tsk - (task_cost tsk - (task_last_nonpr_segment tsk - 1)))) +
        total_ohep_request_bound_function_FP ts (FP := FP) tsk (A + F) ≤ A + F
    rw [hEq]; exact hF
  · show F + (task_cost tsk - (task_cost tsk - (task_last_nonpr_segment tsk - 1))) ≤ R
    rw [hEq]; exact hFR

end Prosa.Results.Rta.Ideal.Fp.LimitedPreemptive
