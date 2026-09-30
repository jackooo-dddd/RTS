-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ovh/edf/fully_preemptive.v

import Prosa.Results.Rta.Rs.Edf.FullyPreemptive
import Prosa.Model.Composite.ValidTaskArrivalSequence
import Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp

namespace Prosa.Results.Rta.Ovh.Edf.FullyPreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.AbsoluteDeadline
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Task.Preemption.FullyPreemptive
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Edf
open Prosa.Model.Readiness.Basic
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.PlatformProperties
open Prosa.Util.Minmax
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Edf
open Prosa.Analysis.Definitions.Workload.EdfAthepBound
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Abstract.RestrictedSupply.IwInstantiation
open Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf
open Prosa.Analysis.Facts.Behavior.Arrivals
open Prosa.Analysis.Facts.Behavior.Completion
open Prosa.Analysis.Facts.Model.ArrivalCurves
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Analysis.Facts.Priority.Edf
open Prosa.Analysis.Facts.Readiness.Basic
open Prosa.Analysis.Facts.Preemption.Job.Preemptive
open Prosa.Analysis.Facts.Preemption.Task.Preemptive
open Prosa.Analysis.Facts.Preemption.RtcThreshold.Preemptive
open Prosa.Model.Processor.Overheads
open Prosa.Model.Processor.OverheadResourceModel
open Prosa.Util.Sum
open Prosa.Util.UnitGrowth
open Prosa.Model.Composite.ValidTaskArrivalSequence
open Prosa.Analysis.Facts.Model.Overheads.Schedule
open Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp
open Prosa.Model.Priority.Coercion
open Prosa.Analysis.Facts.Workload.EdfAthepBound

/-! Response-time analysis for fully preemptive EDF scheduling of sporadic tasks with arbitrary arrival curves on
a uniprocessor subject to scheduling overheads (dispatch, context switches and cache-related preemption delays).

Binders follow the elaborated source types: each declaration takes the section inputs and hypotheses it uses, in
their elaborated order. The processor model is the accepted explicit-overhead processor state; the source's
section-local readiness instance is the accepted `basic_ready_instance` and its preemption model the accepted `fully_preemptive_job_model`, passed
explicitly where the elaborated statement uses them implicitly; the JLFP policy is the accepted EDF instance with deadlines from the task deadlines. The source's section-local
`overhead_bound` (a `Let`) is inlined as a `let` in the two definitions, as in their elaborated bodies. Representation:
a Boolean in `Prop` position is `= true`; `x \in xs` is `decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`;
`\sum_(tsk_o <- ts) F` is `sumSeq ts F`.

The proof instantiates the accepted restricted-supply analysis with the overheads processor model and the accepted
slowed overhead SBF of `analysis/facts/model/overheads/sbf/jlfp.v` (validity, monotonicity and
unit supply are its accepted facts); the overhead bound is the blackout bound, which bounds its slowed version from
above. -/

/-- `L` is a positive solution of the busy-window recurrence with the overhead bound. -/
def busy_window_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (DB CSB CRPDB : duration) (L : duration) : Prop :=
  let overhead_bound := fun Δ : duration => (DB + CSB + CRPDB) * (1 + 2 * sumSeq ts (fun tsk_o => max_arrivals tsk_o Δ))
  0 < L ∧ overhead_bound L + total_request_bound_function ts L ≤ L

/-- `R` solves the response-time recurrence with the overhead bound for every offset of the search space. -/
def rta_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskDeadline Task] [MaxArrivals Task]
    (ts : List Task) (tsk : Task) (DB CSB CRPDB : duration) (L : duration) (R : Nat) : Prop :=
  let overhead_bound := fun Δ : duration => (DB + CSB + CRPDB) * (1 + 2 * sumSeq ts (fun tsk_o => max_arrivals tsk_o Δ))
  ∀ A : duration, @is_in_search_space Task _ _ _ fully_preemptive_task_model ts _ tsk L A = true →
    ∃ F : duration,
      overhead_bound F + task_request_bound_function tsk (A + 1) + bound_on_athep_workload ts tsk A F ≤ F ∧
      F ≤ A + R

/-- LEAN_HELPER: a demand fitting in the interval together with the blackout bound fits in the slowed SBF. -/
private theorem ovh_sbf_lower (f : Nat → Nat) (x Δ : Nat) (h : f Δ + x ≤ Δ) : x ≤ Δ - slowed f Δ := by
  have := slowed_never_exceeds f Δ
  omega

/-- LEAN_HELPER: `ovh_sbf_lower` for a two-term demand. -/
private theorem ovh_sbf_lower2 (f : Nat → Nat) (x y Δ : Nat) (h : f Δ + x + y ≤ Δ) :
    x + y ≤ Δ - slowed f Δ :=
  ovh_sbf_lower f (x + y) Δ (by omega)

/-- LEAN_HELPER: `ovh_sbf_lower` for a three-term demand. -/
private theorem ovh_sbf_lower3 (f : Nat → Nat) (x y z Δ : Nat) (h : f Δ + x + y + z ≤ Δ) :
    x + y + z ≤ Δ - slowed f Δ :=
  ovh_sbf_lower f (x + y + z) Δ (by omega)

/-- Response-time bound for fully preemptive EDF scheduling on a unit-speed uniprocessor subject to scheduling
overheads. -/
theorem uniprocessor_response_time_bound_fully_preemptive_edf {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [TaskDeadline Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task]
    [JobCost Job] [JobArrival Job] (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ arr_seq : arrival_sequence Job, valid_task_arrival_sequence ts arr_seq →
      arrivals_have_positive_job_costs arr_seq →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @respects_JLFP_policy_at_preemption_point Job _ _ _ (processor_state Job) fully_preemptive_job_model
        basic_ready_instance arr_seq sched (@EDF Job _ (job_deadline_from_task_deadline Job Task)) →
      @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := @EDF Job _ (job_deadline_from_task_deadline Job Task)))
        (processor_state Job) sched →
    ∀ DB CSB CRPDB : duration, overhead_resource_model sched DB CSB CRPDB →
    ∀ L : duration, busy_window_recurrence_solution ts DB CSB CRPDB L →
    ∀ R : duration, rta_recurrence_solution ts tsk DB CSB CRPDB L R →
      task_response_time_bound arr_seq sched tsk R := by
  intro hin arr_seq hvtas hpos sched hvs hwc hresp hnsp DB CSB CRPDB horm L hbw R hsol
  have hva := valid_task_arrival_sequence_valid_arrivals ts arr_seq hvtas
  have hcost := valid_task_arrival_sequence_valid_costs ts arr_seq hvtas
  have hall := valid_task_arrival_sequence_from_taskset ts arr_seq hvtas
  have hrespma := valid_task_arrival_sequence_respects_max ts arr_seq hvtas
  have hvalid := valid_task_arrival_sequence_valid_curve ts arr_seq hvtas
  let _ : JobReady Job (processor_state Job) := basic_ready_instance
  let _ : JobPreemptable Job := fully_preemptive_job_model
  have hvpm := valid_fully_preemptive_model arr_seq sched
  have hsbf := overheads_sbf_busy_valid (@EDF Job _ (job_deadline_from_task_deadline Job Task)) EDF_is_reflexive EDF_is_transitive arr_seq hva sched
    hvs hwc hnsp hresp hvpm ts hall hrespma hpos DB CSB CRPDB horm tsk
  obtain ⟨hL, hfix⟩ := hbw
  refine Prosa.Results.Rta.Rs.Edf.FullyPreemptive.uniprocessor_response_time_bound_fully_preemptive_edf
    overheads_proc_model_is_a_uniprocessor_model overheads_proc_model_provides_unit_supply
    overheads_proc_model_fully_consuming
    arr_seq hva hcost ts hall
    hrespma hvalid tsk hin sched
    hvs hwc
    hresp
    (jlfp_ovh_sbf_slow ts DB CSB CRPDB)
    (overheads_sbf_monotone ts DB CSB CRPDB)
    (overheads_sbf_unit ts hvalid DB CSB CRPDB) hsbf L ⟨hL, ovh_sbf_lower (jlfp_blackout_bound ts DB CSB CRPDB) _ L hfix⟩ R ?_
  intro A hA
  obtain ⟨F, hF, hFR⟩ := hsol A hA
  exact ⟨F, ovh_sbf_lower2 (jlfp_blackout_bound ts DB CSB CRPDB) _ _ F hF, hFR⟩

end Prosa.Results.Rta.Ovh.Edf.FullyPreemptive
