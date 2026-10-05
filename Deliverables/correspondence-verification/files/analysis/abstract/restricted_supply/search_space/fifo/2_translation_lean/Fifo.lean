-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/search_space/fifo.v

import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Abstract.SearchSpace
import Prosa.Analysis.Facts.Priority.Fifo
import Prosa.Analysis.Definitions.Sbf.Pred

namespace Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.Sbf
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Facts.Model.Rbf

/-! The abstract search space is a subset of the restricted-supply FIFO
search space. Binders follow the elaborated source types (unused section
context and hypotheses are absent, as in the elaborated source).
Representation: `ε` is `1`; the section-local `rbf` and the local `let
rbf_makes_a_step` are inlined; the source's `Local Definition IBF` (printed as
`fifo.IBF ts tsk` in the elaborated statement) is inlined as the function
`fun A F => F - SBF F + (total_rbf ts (A + 1) - task_cost tsk)`; the supply
bound function is applied through its accepted class field; `a != b` is
`decide (a ≠ b)`; `has p xs` is `xs.any p`; `x \in xs` in `Prop` position is
`decide (x ∈ xs) = true`; `search_space.is_in_search_space` is the accepted
abstract search-space predicate. -/

/-- The FIFO search space: offsets below `L` where the RBF of some task of
`ts` makes a step. -/
def is_in_search_space {Task : TaskType} [DecidableEq Task] [TaskCost Task] (ts : List Task)
    [MaxArrivals Task] (L A : duration) : Bool :=
  decide (A < L) &&
    ts.any (fun tsk => decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + 1)))

theorem search_space_sub (SBF : SupplyBoundFunction) {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    (ts : List Task) [MaxArrivals Task] :
    valid_taskset_arrival_curve ts max_arrivals →
      ∀ L : duration, 0 < L →
        ∀ tsk : Task, decide (tsk ∈ ts) = true → 0 < task_cost tsk → 0 < max_arrivals tsk 1 →
          ∀ A : Nat,
            Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                (fun A0 F : duration => F - SBF.supply_bound_function F +
                  (total_request_bound_function ts (A0 + 1) - task_cost tsk)) A →
              is_in_search_space ts L A = true := by
  intro hv L hL tsk hin hc hpos A h
  unfold is_in_search_space
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rcases h with hA | ⟨hA0, hAL, x, _, hne⟩
  · subst hA
    refine ⟨hL, ?_⟩
    rw [List.any_eq_true]
    refine ⟨tsk, of_decide_eq_true hin, ?_⟩
    have h0 := task_rbf_0_zero tsk (hv tsk hin)
    have h1 := task_rbf_epsilon_gt_0 tsk hc hpos
    apply decide_eq_true
    rw [h0, Nat.zero_add]
    exact Nat.ne_of_lt h1
  · refine ⟨hAL, ?_⟩
    by_contra hcon
    apply hne
    have hA1 : A - 1 + 1 = A := Nat.sub_add_cancel hA0
    show x - SBF.supply_bound_function x + (total_request_bound_function ts (A - 1 + 1) - task_cost tsk) =
      x - SBF.supply_bound_function x + (total_request_bound_function ts (A + 1) - task_cost tsk)
    rw [hA1]
    congr 2
    unfold total_request_bound_function sumSeq
    apply congrArg List.sum
    apply List.map_congr_left
    intro o ho
    by_contra hd
    apply hcon
    rw [List.any_eq_true]
    exact ⟨o, ho, decide_eq_true hd⟩

end Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo
