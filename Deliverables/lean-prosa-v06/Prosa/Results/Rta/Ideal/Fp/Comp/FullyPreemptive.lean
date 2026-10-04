-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: results/rta/ideal/fp/comp/fully_preemptive.v

import Prosa.Util.Fixpoint
import Prosa.Results.Rta.Ideal.Fp.FullyPreemptive

namespace Prosa.Results.Rta.Ideal.Fp.Comp.FullyPreemptive

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Ready
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Preemption.FullyPreemptive
open Prosa.Model.Priority.Definitions
open Prosa.Model.Processor.Ideal
open Prosa.Model.Readiness.Sequential
open Prosa.Model.Schedule.PriorityDriven
open Prosa.Analysis.Definitions.Schedulability
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Facts.Model.Rbf
open Prosa.Util.Fixpoint

/-! RTA for fully preemptive FP scheduling on ideal uniprocessors with computed fixpoints.

Binders follow the elaborated source type. The section's readiness (the accepted `sequential_ready_instance` at the
arrival sequence, the local `sequential_readiness`) and the accepted `fully_preemptive_job_model` are passed
explicitly where the elaborated statement uses them implicitly (the fully preemptive task model and run-to-completion
threshold are not part of the statement). The section-local `is_in_search_space` is the accepted
`Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space tsk L` and `recurrence` is inlined. Representation: `Some` is
`some`; a Boolean in `Prop` position is `= true`; `x \in xs` is `decide (x ∈ xs) = true`; `ε` is `1`. -/

/-- `omega` after unfolding the time aliases. -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration, work] at *) <;> omega)

/-- Response-time bound for fully preemptive FP scheduling, with `L` and `R` found by the fixpoint searches. -/
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
      @Prosa.Model.Schedule.WorkConserving.work_conserving Job _ _ _ (processor_state Job)
        (sequential_ready_instance (Task := Task) arr_seq) arr_seq sched →
    ∀ FP : FP_policy Task, reflexive_task_priorities FP → transitive_task_priorities FP →
      @respects_FP_policy_at_preemption_point Task _ Job _ _ _ _ (processor_state Job) fully_preemptive_job_model
        (sequential_ready_instance (Task := Task) arr_seq) arr_seq sched FP →
    ∀ (h : Nat) (L : duration), some L = find_fixpoint (total_hep_request_bound_function_FP ts (FP := FP) tsk) h →
    ∀ R : duration,
      some R = find_max_fixpoint L (Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space tsk L)
        (fun A F => task_request_bound_function tsk (A + 1) +
          total_ohep_request_bound_function_FP ts (FP := FP) tsk (A + F) - A) h →
      task_response_time_bound arr_seq sched tsk R := by
  intro hva ts hall hvjc _ hvalid hresp tsk hin sched hvs hwc FP hrefl htrans hrespFP h L hL R hR
  by_cases h0 : total_hep_request_bound_function_FP ts (FP := FP) tsk 1 ≤ 0
  · exact pathological_total_hep_rbf_any_bound ts arr_seq hvjc hresp (processor_state Job) sched FP hrefl tsk hin
      (by omega') R
  · have hpos : 0 < L :=
      ffp_finds_positive_fixpoint _ h (total_hep_rbf_monotone ts hvalid FP tsk) (by omega') L hL
    have hfix : L = total_hep_request_bound_function_FP ts (FP := FP) tsk L := ffp_finds_fixpoint _ h L hL.symm
    refine Prosa.Results.Rta.Ideal.Fp.FullyPreemptive.uniprocessor_response_time_bound_fully_preemptive_fp arr_seq
      hva ts hall hvjc hvalid hresp tsk hin sched hvs FP hrefl htrans hwc hrespFP L hpos hfix R ?_
    intro A hA
    have hlt : A < L := by
      unfold Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space at hA
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hA
      exact hA.1
    obtain ⟨F, hF, hFR⟩ := fmf_is_maximum L _ _ h A R hR ⟨hlt, hA⟩
    have hFfix := ffp_finds_fixpoint _ h F hF.symm
    exact ⟨F, by omega', hFR⟩

end Prosa.Results.Rta.Ideal.Fp.Comp.FullyPreemptive
