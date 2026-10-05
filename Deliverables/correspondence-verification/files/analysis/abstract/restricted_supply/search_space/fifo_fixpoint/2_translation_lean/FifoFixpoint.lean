-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/search_space/fifo_fixpoint.v

import Prosa.Model.Priority.Fifo
import Prosa.Model.Task.Preemption.Parameters
import Prosa.Analysis.Definitions.Sbf.Busy
import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo

namespace Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.FifoFixpoint

open Prosa.Behavior.Arrival_sequence
open Prosa.Behavior.Job
open Prosa.Behavior.Schedule
open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Preemption.Parameter
open Prosa.Model.Priority.Fifo
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.Sbf.Pred
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo
open Prosa.Analysis.Facts.Model.Rbf

/-! A solution of the concrete FIFO response-time recurrence yields a solution
of the abstract restricted-supply recurrence.

Binders follow the elaborated source type: the section inputs and hypotheses
the lemma uses, in their elaborated order (the unused
`TaskMaxNonpreemptiveSegment` context is absent, as in the elaborated type).
The JLFP policy of the busy-SBF validity is the accepted global FIFO
instance; the busy-SBF validity is the classical one of
`analysis/definitions/sbf/busy.v` and the supply bound function is applied
through its accepted class field. The source's `Local Definition intra_IBF`
(printed as `fifo_fixpoint.intra_IBF ts tsk` in the elaborated statement) is
inlined as `total_rbf ts (A + 1) - task_cost tsk`, and the FIFO
`fifo.IBF ts tsk` as the accepted FIFO search-space function. Representation:
a Boolean in `Prop` position is `= true`; `x \in xs` is
`decide (x ∈ xs) = true`; `a >= b` is `b ≤ a`; `ε` is `1`. -/

/-- A unit-growth function starting at zero takes every value up to `f n`
somewhere in `[0, n]`. -/
private theorem exists_intermediate_value (f : Nat → Nat) (hunit : ∀ t, f (t + 1) ≤ f t + 1)
    (h0 : f 0 = 0) : ∀ (n v : Nat), v ≤ f n → ∃ m, m ≤ n ∧ f m = v := by
  intro n
  induction n with
  | zero => intro v hv; exact ⟨0, Nat.le_refl _, by omega⟩
  | succ n ih =>
    intro v hv
    by_cases h : v ≤ f n
    · obtain ⟨m, hm, hfm⟩ := ih v h
      exact ⟨m, by omega, hfm⟩
    · have := hunit n
      exact ⟨n + 1, Nat.le_refl _, by omega⟩

theorem soln_abstract_response_time_recurrence {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [MaxArrivals Task] [TaskRunToCompletionThreshold Task] {Job : JobType} [DecidableEq Job]
    [JobTask Job Task] [JobCost Job] [JobArrival Job] [JobPreemptable Job] {PState : ProcessorState Job}
    (SBF : SupplyBoundFunction) :
    sbf_is_monotone SBF.supply_bound_function → unit_supply_bound_function SBF.supply_bound_function →
    ∀ (ts : List Task) (tsk : Task), decide (tsk ∈ ts) = true →
    ∀ arr_seq : arrival_sequence Job, valid_taskset_arrival_curve ts max_arrivals →
    ∀ sched : schedule PState,
      @Prosa.Analysis.Definitions.Sbf.Busy.valid_busy_sbf Task _ Job _ _ _ _ PState arr_seq sched
        (FIFO Job) tsk SBF.supply_bound_function →
      valid_task_run_to_completion_threshold arr_seq tsk →
    ∀ L : duration, 0 < L → 0 < task_cost tsk → 0 < max_arrivals tsk 1 →
    ∀ R : duration,
      (∀ A : duration, is_in_search_space ts L A = true →
        ∃ F : duration, total_request_bound_function ts (A + 1) ≤ SBF.supply_bound_function F ∧ F ≤ A + R) →
    ∀ A : duration,
      Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
          (fun A0 F : duration => F - SBF.supply_bound_function F +
            (total_request_bound_function ts (A0 + 1) - task_cost tsk)) A →
      ∃ F : duration, F ≤ A + R ∧
        task_rtct tsk + (total_request_bound_function ts (A + 1) - task_cost tsk) ≤ SBF.supply_bound_function F ∧
        SBF.supply_bound_function F + (task_cost tsk - task_rtct tsk) ≤ SBF.supply_bound_function (A + R) := by
  intro hmono hunit ts tsk hin arr_seq hvalid sched hsbf hrtc L hL hc hpos R hmax A hsp
  obtain ⟨F', hF', hF'le⟩ := hmax A (search_space_sub SBF ts hvalid L hL tsk hin hc hpos A hsp)
  have hleq1 := of_decide_eq_true (hmono F' (A + R) (decide_eq_true hF'le))
  have hleq2 := task_cost_le_sum_rbf tsk (hvalid tsk hin) hpos ts hin (A + 1) (Nat.succ_pos _)
  have hleq3 : task_rtct tsk ≤ task_cost tsk := of_decide_eq_true hrtc.1
  obtain ⟨F, hFle, hFeq⟩ := exists_intermediate_value SBF.supply_bound_function hunit hsbf.1 (A + R)
    (SBF.supply_bound_function (A + R) - (task_cost tsk - task_rtct tsk)) (Nat.sub_le _ _)
  refine ⟨F, hFle, ?_, ?_⟩ <;> rw [hFeq] <;> omega'

end Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.FifoFixpoint
