-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ovh/fp/fully_preemptive.v

import Prosa.Results.Rta.Rs.Fp.FullyPreemptive
import Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp
import Prosa.Analysis.Facts.Model.TaskArrivals
import Prosa.Model.Composite.ValidTaskArrivalSequence

namespace Prosa.Results.Rta.Ovh.Fp.FullyPreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Service
open Prosa.Behavior.Time
open Prosa.Model.Job.Properties
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrivals
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Sequentiality
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Coercion
open Prosa.Model.Readiness.Basic
open Prosa.Model.Readiness.Sequential
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Model.Processor.Overheads
open Prosa.Model.Processor.OverheadResourceModel
open Prosa.Util.Sum
open Prosa.Util.UnitGrowth
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp
open Prosa.Model.Composite.ValidTaskArrivalSequence
open Prosa.Analysis.Facts.Model.TaskArrivals
open Prosa.Analysis.Facts.Preemption.Job.Preemptive
open Prosa.Analysis.Facts.Model.Overheads.Schedule
open Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp

/-! Response-time analysis for fully preemptive fixed-priority scheduling of sporadic tasks with arbitrary arrival
curves on a uniprocessor subject to scheduling overheads.

Binders follow the elaborated source types: each declaration takes the section inputs and hypotheses it uses, in
their elaborated order. The processor model is the accepted explicit-overhead processor state; the source's
section-local readiness instance is the accepted `basic_ready_instance` and its preemption model the accepted
`fully_preemptive_job_model`, passed explicitly where the elaborated statement uses them implicitly; the FP policy
acts on jobs through the accepted `FP_to_JLFP`. The source's section-local `overhead_bound` (a `Let`) is inlined
as a `let` in the two definitions, as in their elaborated bodies; `is_in_search_space` is the accepted FP search
space. Representation: a Boolean in `Prop` position is `= true`; `x \in xs` is `decide (x ∈ xs) = true`;
`a >= b` is `b ≤ a`; `ε` is `1`; a filtered sum `\sum_(x <- xs | P x) F x` is `sumFiltered xs P F`.

The proof instantiates the accepted restricted-supply FP analysis with the overheads processor model and the
accepted slowed FP overhead SBF (validity, monotonicity and unit supply are the accepted facts of
`analysis/facts/model/overheads/sbf/fp.v`); that analysis is stated for the sequential readiness model, whose
validity, work conservation and policy compliance follow from those of the basic readiness model together with
the sequential-tasks hypothesis (private helpers below). The overhead bound is the FP blackout bound, which bounds
its slowed version from above. -/

/-- `L` is a positive solution of the busy-window recurrence with the FP overhead bound. -/
def busy_window_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (tsk : Task) [FP : FP_policy Task] (DB CSB CRPDB : duration) (L : duration) : Prop :=
  let overhead_bound := fun Δ : duration =>
    (DB + CSB + CRPDB) * (1 + 2 * sumFiltered ts (fun tsk_o => hep_task tsk_o tsk) (fun tsk_o => max_arrivals tsk_o Δ))
  0 < L ∧ overhead_bound L + total_hep_request_bound_function_FP ts tsk L ≤ L

/-- `R` solves the response-time recurrence with the FP overhead bound for every offset of the search space. -/
def rta_recurrence_solution {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (ts : List Task) (tsk : Task) [FP : FP_policy Task] (DB CSB CRPDB : duration) (L : duration) (R : Nat) : Prop :=
  let overhead_bound := fun Δ : duration =>
    (DB + CSB + CRPDB) * (1 + 2 * sumFiltered ts (fun tsk_o => hep_task tsk_o tsk) (fun tsk_o => max_arrivals tsk_o Δ))
  ∀ A : duration, is_in_search_space tsk L A = true →
    ∃ F : duration,
      overhead_bound F + task_request_bound_function tsk (A + 1) + total_ohep_request_bound_function_FP ts tsk F ≤ F ∧
      F ≤ A + R

section SequentialReadiness

variable {Task : TaskType} [DecidableEq Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobArrival Job]
  [JobCost Job] {PState : ProcessorState Job} (arr_seq : arrival_sequence Job) (sched : schedule PState)

/-- LEAN_HELPER: a sequential-readiness backlog is a basic-readiness backlog. -/
private theorem ovh_seq_backlogged (j : Job) (t : instant)
    (h : @backlogged Job _ PState _ _ (sequential_ready_instance (Task := Task) arr_seq) sched j t = true) :
    @backlogged Job _ PState _ _ basic_ready_instance sched j t = true := by
  have h1 : (pending sched j t && prior_jobs_complete (Task := Task) arr_seq sched j t &&
      !scheduled_at sched j t) = true := h
  show (pending sched j t && !scheduled_at sched j t) = true
  revert h1
  cases pending sched j t <;> cases prior_jobs_complete (Task := Task) arr_seq sched j t <;> simp

/-- LEAN_HELPER: under sequential tasks, a basic-valid schedule is valid for the sequential readiness model. -/
private theorem ovh_seq_valid_schedule (hc : consistent_arrival_times arr_seq)
    (hvs : @valid_schedule Job _ _ PState sched _ basic_ready_instance arr_seq)
    (hseq : sequential_tasks (Task := Task) arr_seq sched) :
    @valid_schedule Job _ _ PState sched _ (sequential_ready_instance (Task := Task) arr_seq) arr_seq := by
  refine ⟨hvs.1, fun j t hs => ?_⟩
  show (pending sched j t && prior_jobs_complete (Task := Task) arr_seq sched j t) = true
  have hpend : pending sched j t = true := hvs.2 j t hs
  rw [hpend, Bool.true_and]
  unfold prior_jobs_complete
  rw [List.all_eq_true]
  intro jo hjo
  have hmem : decide (jo ∈ task_arrivals_before arr_seq (job_task (Task := Task) j) (job_arrival j)) = true :=
    decide_eq_true hjo
  exact hseq jo j t (arrives_in_task_arrivals_implies_arrived arr_seq _ 0 _ jo hmem) (hvs.1 j t hs)
    (by
      unfold same_task
      have := arrives_in_task_arrivals_implies_job_task arr_seq _ jo _ hmem
      simpa using this)
    (arrives_in_task_arrivals_before_implies_arrives_before arr_seq hc _ jo _ hmem) hs

/-- LEAN_HELPER: work conservation carries over from basic to sequential readiness. -/
private theorem ovh_seq_work_conserving
    (hwc : @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ PState basic_ready_instance arr_seq sched) :
    @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ PState
      (sequential_ready_instance (Task := Task) arr_seq) arr_seq sched :=
  fun j t ha hb => hwc j t ha (ovh_seq_backlogged arr_seq sched j t hb)

/-- LEAN_HELPER: compliance with a JLDP policy at preemption points carries over from basic to sequential
readiness. -/
private theorem ovh_seq_respects [JobPreemptable Job] (P : JLDP_policy Job)
    (h : @respects_JLDP_policy_at_preemption_point Job _ _ _ PState _ basic_ready_instance arr_seq sched P) :
    @respects_JLDP_policy_at_preemption_point Job _ _ _ PState _ (sequential_ready_instance (Task := Task) arr_seq)
      arr_seq sched P :=
  fun j jhp t ha hpt hb hs => h j jhp t ha hpt (ovh_seq_backlogged arr_seq sched j t hb) hs

end SequentialReadiness

/-- Response-time bound for fully preemptive FP scheduling on a unit-speed uniprocessor subject to scheduling
overheads. -/
theorem uniprocessor_response_time_bound_fully_preemptive_fp {Task : TaskType} [DecidableEq Task]
    [TaskCost Task] [MaxArrivals Task] {Job : JobType} [DecidableEq Job] [JobTask Job Task] [JobCost Job]
    [JobArrival Job] (ts : List Task) (tsk : Task) :
    decide (tsk ∈ ts) = true →
    ∀ arr_seq : arrival_sequence Job, valid_task_arrival_sequence ts arr_seq →
      arrivals_have_positive_job_costs arr_seq →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
    ∀ sched : schedule (processor_state Job),
      @valid_schedule Job _ _ (processor_state Job) sched _ basic_ready_instance arr_seq →
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job) basic_ready_instance
        arr_seq sched →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ (processor_state Job) fully_preemptive_job_model
        basic_ready_instance arr_seq sched FP →
      sequential_tasks (Task := Task) arr_seq sched →
      @no_superfluous_preemptions Job _ _ (JLFP_to_JLDP (JLFP := FP_to_JLFP FP)) (processor_state Job) sched →
    ∀ DB CSB CRPDB : duration, overhead_resource_model sched DB CSB CRPDB →
    ∀ L : duration, busy_window_recurrence_solution ts tsk (FP := FP) DB CSB CRPDB L →
    ∀ R : duration, rta_recurrence_solution ts tsk (FP := FP) DB CSB CRPDB L R →
      task_response_time_bound arr_seq sched tsk R := by
  intro hin arr_seq hvtas hpos FP hrefl htrans sched hvs hwc hrespFP hseq hnsp DB CSB CRPDB horm L hbw R hsol
  have hva := valid_task_arrival_sequence_valid_arrivals ts arr_seq hvtas
  have hcost := valid_task_arrival_sequence_valid_costs ts arr_seq hvtas
  have hall := valid_task_arrival_sequence_from_taskset ts arr_seq hvtas
  have hresp := valid_task_arrival_sequence_respects_max ts arr_seq hvtas
  have hvalid := valid_task_arrival_sequence_valid_curve ts arr_seq hvtas
  let _ : JobPreemptable Job := fully_preemptive_job_model
  have hvpm := valid_fully_preemptive_model arr_seq sched
  have hsbf := overheads_sbf_busy_valid FP hrefl htrans arr_seq hva sched hvs hwc hnsp hrespFP hvpm ts hall hresp
    hpos DB CSB CRPDB horm tsk
  obtain ⟨hL, hfix⟩ := hbw
  have hslow := slowed_never_exceeds (fp_blackout_bound (FP := FP) ts DB CSB CRPDB tsk) L
  refine Prosa.Results.Rta.Rs.Fp.FullyPreemptive.uniprocessor_response_time_bound_fully_preemptive_fp
    overheads_proc_model_is_a_uniprocessor_model overheads_proc_model_provides_unit_supply
    overheads_proc_model_fully_consuming arr_seq hva hcost ts hall hresp hvalid tsk hin sched
    (ovh_seq_valid_schedule arr_seq sched hva.1 hvs hseq) (ovh_seq_work_conserving arr_seq sched hwc)
    FP hrefl htrans (ovh_seq_respects arr_seq sched _ hrespFP)
    (fp_ovh_sbf_slow (FP := FP) ts DB CSB CRPDB tsk) (overheads_sbf_monotone FP ts DB CSB CRPDB tsk)
    (overheads_sbf_unit FP ts hvalid DB CSB CRPDB tsk) hsbf L ⟨hL, ?_⟩ R ?_
  · show total_hep_request_bound_function_FP ts (FP := FP) tsk L ≤
      L - slowed (fp_blackout_bound (FP := FP) ts DB CSB CRPDB tsk) L
    have : fp_blackout_bound (FP := FP) ts DB CSB CRPDB tsk L + total_hep_request_bound_function_FP ts (FP := FP) tsk L
        ≤ L := hfix
    omega
  · intro A hA
    obtain ⟨F, hF, hFR⟩ := hsol A hA
    refine ⟨F, ?_, hFR⟩
    have hs := slowed_never_exceeds (fp_blackout_bound (FP := FP) ts DB CSB CRPDB tsk) F
    show task_request_bound_function tsk (A + 1) + total_ohep_request_bound_function_FP ts (FP := FP) tsk F ≤
      F - slowed (fp_blackout_bound (FP := FP) ts DB CSB CRPDB tsk) F
    have : fp_blackout_bound (FP := FP) ts DB CSB CRPDB tsk F + task_request_bound_function tsk (A + 1) +
        total_ohep_request_bound_function_FP ts (FP := FP) tsk F ≤ F := hF
    omega

end Prosa.Results.Rta.Ovh.Fp.FullyPreemptive
