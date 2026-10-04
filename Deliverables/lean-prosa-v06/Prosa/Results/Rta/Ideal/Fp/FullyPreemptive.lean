-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/fp/fully_preemptive.v

import Prosa.Results.Rta.Ideal.Fp.BoundedNps
import Prosa.Analysis.Facts.Preemption.Task.Preemptive
import Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive
import Prosa.Analysis.Facts.Readiness.Sequential

namespace Prosa.Results.Rta.Ideal.Fp.FullyPreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.FullyPreemptive
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyPreemptive
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
open Prosa.Analysis.Facts.Preemption.Job.Preemptive
open Prosa.Analysis.Facts.Preemption.Task.Preemptive
open Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive

/-! RTA for fully preemptive FP scheduling on ideal uniprocessors.

Binders follow the elaborated source type. The source's section-local instances are passed explicitly where the
elaborated statement uses them implicitly: the accepted `fully_preemptive_job_model` and the accepted
`sequential_ready_instance arr_seq` (the local `sequential_readiness`); `fully_preemptive_task_model` and
`fully_preemptive_rtc_threshold` are used by the proof. The section-local `rbf`, `task_rbf`, `total_hep_rbf`,
`total_ohep_rbf` and the local search-space abbreviation are inlined; `fp.bounded_pi.is_in_search_space` is the
accepted `Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space`. Representation: a Boolean in `Prop` position is
`= true`; `x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`. -/

/-- The FP blocking bound vanishes in the fully preemptive task model. -/
private theorem blocking_bound_fully_preemptive {Task : TaskType} [DecidableEq Task] (FP : FP_policy Task)
    (ts : List Task) (tsk : Task) :
    @blocking_bound Task _ fully_preemptive_task_model FP ts tsk = 0 := by
  unfold blocking_bound bigMaxListCond
  induction ts with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    split <;> rfl

theorem uniprocessor_response_time_bound_fully_preemptive_fp {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job] [JobCost Job]
    (arr_seq : arrival_sequence Job) :
    valid_arrival_sequence arr_seq →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals → taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ (sequential_ready_instance (Task := Task) arr_seq)
        arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job)
        (sequential_ready_instance (Task := Task) arr_seq) arr_seq sched →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ (processor_state Job) fully_preemptive_job_model
        (sequential_ready_instance (Task := Task) arr_seq) arr_seq sched FP →
    ∀ L : duration, 0 < L → L = total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ R : duration,
      (∀ A : duration, Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space tsk L A = true →
        ∃ F : duration,
          task_request_bound_function tsk (A + 1) + total_ohep_request_bound_function_FP ts (FP := FP) tsk (A + F) ≤
            A + F ∧ F ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva ts hall hcost _ hvalid hresp tsk hin sched hvs FP hrefl htrans hwc hrespFP L hL hfix R hR
  let _ : JobReady Job (processor_state Job) := sequential_ready_instance (Task := Task) arr_seq
  let _ : JobPreemptable Job := fully_preemptive_job_model
  let _ : TaskMaxNonpreemptiveSegment Task := fully_preemptive_task_model
  let _ : TaskRunToCompletionThreshold Task := fully_preemptive_rtc_threshold
  have hB := blocking_bound_fully_preemptive FP ts tsk
  have hwb := sequential_readiness_implies_work_bearing_readiness (Task := Task) arr_seq hva.1 sched FP hrefl
  have hvpm := valid_fully_preemptive_model arr_seq sched
  have hvm : valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched :=
    ⟨hvpm, fully_preemptive_model_is_model_with_bounded_nonpreemptive_regions arr_seq⟩
  refine Prosa.Results.Rta.Ideal.Fp.BoundedNps.uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments
    hrefl htrans arr_seq hva sched hwb hvs hvm hwc hrespFP
    (sequential_readiness_implies_sequential_tasks arr_seq hva.1 sched hvs) ts hall hcost hvalid hresp tsk hin hvpm
    (fully_preemptive_valid_task_run_to_completion_threshold arr_seq hcost tsk) L hL
    (by rw [hB, Nat.zero_add]; exact hfix) R ?_
  intro A hA
  obtain ⟨F, hF, hFR⟩ := hR A hA
  refine ⟨F, ?_, ?_⟩
  · show blocking_bound ts tsk + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_cost tsk)) +
        total_ohep_request_bound_function_FP ts (FP := FP) tsk (A + F) ≤ A + F
    rw [hB]; ((try dsimp only [instant, duration, work] at *) <;> omega)
  · show F + (task_cost tsk - task_cost tsk) ≤ R
    ((try dsimp only [instant, duration, work] at *) <;> omega)

end Prosa.Results.Rta.Ideal.Fp.FullyPreemptive
