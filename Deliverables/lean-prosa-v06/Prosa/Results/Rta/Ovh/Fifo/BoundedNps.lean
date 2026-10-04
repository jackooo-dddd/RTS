-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ovh/fifo/bounded_nps.v

import Prosa.Results.Rta.Rs.Fifo.BoundedNps
import Prosa.Model.Composite.ValidTaskArrivalSequence
import Prosa.Analysis.Facts.Model.Overheads.Sbf.Fifo

namespace Prosa.Results.Rta.Ovh.Fifo.BoundedNps

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Priority.Fifo
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.Overheads
open Prosa.Model.Processor.OverheadResourceModel
open Prosa.Util.Sum
open Prosa.Util.UnitGrowth
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo
open Prosa.Model.Composite.ValidTaskArrivalSequence
open Prosa.Analysis.Facts.Model.Overheads.Schedule
open Prosa.Analysis.Facts.Model.Overheads.Sbf.Fifo

/-! Response-time analysis for FIFO scheduling of sporadic tasks with arbitrary arrival curves on a uniprocessor
subject to scheduling overheads (dispatch, context switches and cache-related preemption delays).

Binders follow the elaborated source types: each declaration takes the section inputs and hypotheses it uses, in
their elaborated order. The processor model is the accepted explicit-overhead processor state; the source's
section-local readiness instance is the accepted `basic_ready_instance`, passed explicitly where the elaborated
statement uses it implicitly; the JLFP policy is the accepted global FIFO instance. The source's section-local
`overhead_bound` (a `Let`) is inlined as a `let` in the two definitions, as in their elaborated bodies;
`is_in_search_space` is the accepted FIFO search space. Representation: a Boolean in `Prop` position is `= true`;
`x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`; `\sum_(tsk_o <- ts) F` is `sumSeq ts F`.

The proof instantiates the accepted restricted-supply FIFO analysis with the overheads processor model and the
accepted slowed FIFO overhead SBF, whose validity, monotonicity and unit-supply properties are the accepted
facts of `analysis/facts/model/overheads/sbf/fifo.v`; the overhead bound is the FIFO blackout bound, which bounds
its slowed version from above. -/

/-- `L` is a positive solution of the busy-window recurrence with the FIFO overhead bound. -/
def busy_window_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (DB CSB CRPDB : duration) (L : duration) : Prop :=
  let overhead_bound := fun Δ : duration => (DB + CSB + CRPDB) * (1 + sumSeq ts (fun tsk_o => max_arrivals tsk_o Δ))
  0 < L ∧ overhead_bound L + total_request_bound_function ts L ≤ L

/-- `R` solves the response-time recurrence with the FIFO overhead bound for every offset of the search space. -/
def rta_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (DB CSB CRPDB : duration) (L : duration) (R : Nat) : Prop :=
  let overhead_bound := fun Δ : duration => (DB + CSB + CRPDB) * (1 + sumSeq ts (fun tsk_o => max_arrivals tsk_o Δ))
  ∀ A : duration, is_in_search_space ts L A = true →
    ∃ F : duration, overhead_bound F + total_request_bound_function ts (A + 1) ≤ F ∧ F ≤ A + R

/-- Response-time bound for FIFO scheduling on a unit-speed uniprocessor subject to scheduling overheads. -/
theorem uniprocessor_response_time_bound_fifo {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] [TaskRunToCompletionThreshold Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] [JobArrival Job] [JobPreemptable Job] (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ arr_seq : arrival_sequence Job, valid_task_arrival_sequence ts arr_seq →
      valid_task_run_to_completion_threshold arr_seq tsk →
      arrivals_have_positive_job_costs arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      valid_preemption_model arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) _ basic_ready_instance arr_seq sched
        (FIFO Job) →
      @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := FIFO Job)) (processor_state Job) sched →
    ∀ DB CSB CRPDB : duration, overhead_resource_model sched DB CSB CRPDB →
    ∀ L : duration, busy_window_recurrence_solution ts DB CSB CRPDB L →
    ∀ R : duration, rta_recurrence_solution ts DB CSB CRPDB L R →
      task_response_time_bound arr_seq sched tsk R := by
  intro hin arr_seq hvtas hrtc hpos sched hvs hwc hvpm hrespF hnsp DB CSB CRPDB horm L hbw R hsol
  have hva := valid_task_arrival_sequence_valid_arrivals ts arr_seq hvtas
  have hcost := valid_task_arrival_sequence_valid_costs ts arr_seq hvtas
  have hall := valid_task_arrival_sequence_from_taskset ts arr_seq hvtas
  have hresp := valid_task_arrival_sequence_respects_max ts arr_seq hvtas
  have hvalid := valid_task_arrival_sequence_valid_curve ts arr_seq hvtas
  have hfifo : policy_is_FIFO (FIFO Job) := fun _ _ => rfl
  obtain ⟨hL, hfix⟩ := hbw
  have hslow := slowed_never_exceeds (fifo_blackout_bound ts DB CSB CRPDB) L
  refine Prosa.Results.Rta.Rs.Fifo.BoundedNps.uniprocessor_response_time_bound_fifo
    overheads_proc_model_is_a_uniprocessor_model overheads_proc_model_provides_unit_supply
    overheads_proc_model_fully_consuming arr_seq hva hcost ts hall hresp hvalid sched hvs hwc hrespF hvpm tsk hin
    hrtc (fifo_ovh_sbf_slow ts DB CSB CRPDB) (overheads_sbf_monotone ts DB CSB CRPDB)
    (overheads_sbf_unit ts hvalid DB CSB CRPDB)
    (overheads_sbf_busy_valid (FIFO Job) hfifo arr_seq hva sched hvs hwc hnsp hrespF hvpm ts hall hresp hpos
      DB CSB CRPDB horm tsk) L ⟨hL, ?_⟩ R ?_
  · show total_request_bound_function ts L ≤ L - slowed (fifo_blackout_bound ts DB CSB CRPDB) L
    have : fifo_blackout_bound ts DB CSB CRPDB L + total_request_bound_function ts L ≤ L := hfix
    omega
  · intro A hA
    obtain ⟨F, hF, hFR⟩ := hsol A hA
    refine ⟨F, ?_, hFR⟩
    have hs := slowed_never_exceeds (fifo_blackout_bound ts DB CSB CRPDB) F
    show total_request_bound_function ts (A + 1) ≤ F - slowed (fifo_blackout_bound ts DB CSB CRPDB) F
    have : fifo_blackout_bound ts DB CSB CRPDB F + total_request_bound_function ts (A + 1) ≤ F := hF
    omega

end Prosa.Results.Rta.Ovh.Fifo.BoundedNps
