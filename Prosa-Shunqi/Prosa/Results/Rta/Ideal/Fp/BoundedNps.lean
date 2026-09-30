-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/fp/bounded_nps.v

import Prosa.Analysis.Facts.BusyInterval.PiBound
import Prosa.Results.Rta.Ideal.Fp.BoundedPi
import Prosa.Model.Schedule.WorkConserving
import Prosa.Analysis.Definitions.BusyInterval.Classical
import Prosa.Analysis.Definitions.BlockingBound.Fp
import Prosa.Analysis.Facts.BlockingBound.Fp

namespace Prosa.Results.Rta.Ideal.Fp.BoundedNps

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Processor.Ideal
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.PriorityInversion
open Prosa.Analysis.Definitions.WorkBearingReadiness
open Prosa.Analysis.Definitions.BusyInterval.Classical
open Prosa.Analysis.Definitions.BlockingBound.Fp
open Prosa.Analysis.Facts.Model.Ideal.Schedule
open Prosa.Analysis.Facts.BusyInterval.Pi
open Prosa.Util.Notation

/-! RTA for FP schedulers with bounded nonpreemptive segments on ideal uniprocessors.

Binders follow the elaborated source types: every declaration takes only the section inputs and hypotheses it uses,
in their elaborated order; instance inputs quantified after a hypothesis are `∀ [..]` binders at that position. The
JLFP policy induced by the FP policy (`FP_to_JLFP FP`) is passed explicitly to the policy-dependent definitions. The
section-local `task_rbf`, `total_hep_rbf`, `total_ohep_rbf`, `response_time_bounded_by` and the local abbreviation of
the concrete search space are inlined; `fp.bounded_pi.is_in_search_space` is the accepted
`Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space`. Representation: `ε` is `1`; a Boolean in `Prop` position is
`= true`; `tsk \in ts` is `decide (tsk ∈ ts) = true`. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job]

/-- The maximum lower-priority nonpreemptive segment in a busy-interval prefix is bounded by the FP blocking bound. -/
theorem priority_inversion_is_bounded_by_blocking [TaskMaxNonpreemptiveSegment Task] [JobTask Job Task]
    [JobArrival Job] [JobCost Job] [FP : FP_policy Task] (arr_seq : arrival_sequence Job)
    (sched : schedule (processor_state Job)) [JobPreemptable Job] :
    valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
    ∀ (tsk : Task) (j : Job) (t1 t2 : instant), arrives_in arr_seq j → job_of_task tsk j = true →
      @busy_interval_prefix Job _ _ _ (processor_state Job) arr_seq sched (FP_to_JLFP FP) j t1 t2 →
      @max_lp_nonpreemptive_segment Job _ _ arr_seq (FP_to_JLFP FP) _ j t1 ≤ blocking_bound ts tsk := by
  intro hvalid ts hts tsk j t1 _ _ hjt _
  exact Prosa.Analysis.Facts.BlockingBound.Fp.nonpreemptive_segments_bounded_by_blocking FP arr_seq sched hvalid
    ts hts tsk j hjt t1

/-- The priority inversion of the jobs of `tsk` is bounded by the FP blocking bound. -/
theorem priority_inversion_is_bounded [TaskMaxNonpreemptiveSegment Task] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] [FP : FP_policy Task] :
    transitive_task_priorities FP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule (processor_state Job)) [JobReady Job (processor_state Job)],
      @work_bearing_readiness Job _ _ _ (processor_state Job) _ arr_seq sched (FP_to_JLFP FP) →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      respects_FP_policy_at_preemption_point arr_seq sched FP →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts →
    ∀ tsk : Task, valid_preemption_model arr_seq sched →
      @priority_inversion_is_bounded_by Task _ Job _ _ _ _ (processor_state Job) arr_seq sched (FP_to_JLFP FP) tsk
        (constant (blocking_bound ts tsk)) := by
  intro htrans arr_seq hva sched _ hwb hvs _ hvalid hresp ts hts tsk hvpm
  exact Prosa.Analysis.Facts.BusyInterval.PiBound.priority_inversion_is_bounded (Task := Task) arr_seq hva sched
    (FP_to_JLFP FP) (transitive_priorities_FP_implies_JLFP FP htrans) hvalid hwb hvs hresp hvpm tsk
    (constant (blocking_bound ts tsk)) (ideal_proc_model_is_a_uniprocessor_model Job)
    (ideal_proc_model_provides_unit_service Job) (ideal_proc_model_ensures_ideal_progress Job)
    (fun j t1 t2 ha hjt hbip => priority_inversion_is_bounded_by_blocking arr_seq sched hvalid ts hts tsk j t1 t2
      ha hjt hbip)

/-- Response-time bound for FP schedulers with bounded nonpreemptive segments on ideal uniprocessors. -/
theorem uniprocessor_response_time_bound_fp_with_bounded_nonpreemptive_segments [TaskCost Task]
    [TaskRunToCompletionThreshold Task] [TaskMaxNonpreemptiveSegment Task] [JobTask Job Task] [JobArrival Job]
    [JobCost Job] [FP : FP_policy Task] :
    reflexive_task_priorities FP → transitive_task_priorities FP →
    ∀ arr_seq : arrival_sequence Job, valid_arrival_sequence arr_seq →
    ∀ (sched : schedule (processor_state Job)) [JobReady Job (processor_state Job)],
      @work_bearing_readiness Job _ _ _ (processor_state Job) _ arr_seq sched (FP_to_JLFP FP) →
      valid_schedule sched arr_seq →
    ∀ [JobPreemptable Job], valid_model_with_bounded_nonpreemptive_segments (Task := Task) arr_seq sched →
      Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
      respects_FP_policy_at_preemption_point arr_seq sched FP →
      sequential_tasks (Task := Task) arr_seq sched →
    ∀ ts : List Task, all_jobs_from_taskset arr_seq ts → arrivals_have_valid_job_costs (Task := Task) arr_seq →
    ∀ [MaxArrivals Task], valid_taskset_arrival_curve ts max_arrivals → taskset_respects_max_arrivals arr_seq ts →
    ∀ tsk : Task, decide (tsk ∈ ts) = true →
      valid_preemption_model arr_seq sched →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ L : duration, 0 < L →
      L = blocking_bound ts tsk + total_hep_request_bound_function_FP ts (FP := FP) tsk L →
    ∀ R : duration,
      (∀ A : duration, Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space tsk L A = true →
        ∃ F : duration,
          blocking_bound ts tsk + (task_request_bound_function tsk (A + 1) - (task_cost tsk - task_rtct tsk)) +
              total_ohep_request_bound_function_FP ts (FP := FP) tsk (A + F) ≤ A + F ∧
            F + (task_cost tsk - task_rtct tsk) ≤ R) →
      task_response_time_bound arr_seq sched tsk R := by
  intro hrefl htrans arr_seq hva sched _ hwb hvs _ hvalid hwc hresp hseq ts hts hvjc _ hcurve hrespma tsk hin
    hvpm hrtct L hL hfix R hR
  exact Prosa.Results.Rta.Ideal.Fp.BoundedPi.uniprocessor_response_time_bound_fp hrefl arr_seq hva sched hwb hvs
    hwc hseq hvjc ts hts hcurve hrespma tsk hin hvpm hrtct (blocking_bound ts tsk)
    (priority_inversion_is_bounded htrans arr_seq hva sched hwb hvs hvalid hresp ts hts tsk hvpm) L hL hfix R hR

end Prosa.Results.Rta.Ideal.Fp.BoundedNps
