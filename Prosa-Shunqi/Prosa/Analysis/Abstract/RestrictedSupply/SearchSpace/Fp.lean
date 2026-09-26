-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/search_space/fp.v

import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Abstract.SearchSpace
import Prosa.Analysis.Definitions.BlockingBound.Fp

namespace Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Fp
open Prosa.Analysis.Facts.Model.Rbf

/-! The abstract search space is a subset of the restricted-supply FP search
space. Binders follow the elaborated source types (unused section context and
hypotheses are absent, as in the elaborated source). Representation: `ε` is
`1`; the section-local `task_rbf`, `total_ohep_rbf` and `intra_IBF` are
inlined; the section's FP policy is an explicit binder acting as a local
instance; `a != b` is `decide (a ≠ b)`; `x \in xs` in `Prop` position is
`decide (x ∈ xs) = true`; `search_space.is_in_search_space` is the accepted
abstract search-space predicate. -/

/-- The FP search space: offsets below `L` where the RBF of `tsk` steps. -/
def is_in_search_space {Task : TaskType} [DecidableEq Task] [TaskCost Task] [MaxArrivals Task]
    (tsk : Task) (L : duration) (A : Nat) : Bool :=
  decide (A < L) &&
    decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + 1))

theorem search_space_sub {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskMaxNonpreemptiveSegment Task] (FP : FP_policy Task) (ts : List Task) [MaxArrivals Task] :
    valid_taskset_arrival_curve ts max_arrivals →
      ∀ tsk : Task, decide (tsk ∈ ts) = true →
        ∀ L : duration, 0 < L → 0 < task_cost tsk → 0 < max_arrivals tsk 1 →
          ∀ A : Nat,
            Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                (fun A0 F : duration =>
                  task_request_bound_function tsk (A0 + 1) - task_cost tsk +
                    (blocking_bound (FP := FP) ts tsk +
                      total_ohep_request_bound_function_FP ts (FP := FP) tsk F)) A →
              is_in_search_space tsk L A = true := by
  intro hv tsk hin L hL hc hpos A h
  unfold is_in_search_space
  rcases h with hA | ⟨hA0, hAL, x, _, hne⟩
  · subst hA
    have h0 := task_rbf_0_zero tsk (hv tsk hin)
    have h1 := task_rbf_epsilon_gt_0 tsk hc hpos
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hL, ?_⟩
    rw [h0, Nat.zero_add]
    exact Nat.ne_of_lt h1
  · simp only [Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hAL, ?_⟩
    intro heq
    apply hne
    have hA1 : A - 1 + 1 = A := Nat.sub_add_cancel hA0
    simp only [hA1, heq]

end Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp
