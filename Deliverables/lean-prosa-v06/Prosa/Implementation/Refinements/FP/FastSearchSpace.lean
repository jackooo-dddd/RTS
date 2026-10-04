-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/FP/fast_search_space.v

import Prosa.Results.Rta.Ideal.Fp.BoundedNps
import Prosa.Implementation.Refinements.FastSearchSpaceComputation

/-! # A computation-oriented search space for fixed-priority RTA

Representation (as in `ArrivalCurve` and `FastSearchSpaceComputation`): the file-wide `#[local] Existing Instance
NumericFPAscending` is the accepted `NumericFPAscending Task`, passed explicitly; `\sum_(x <- xs | P x) F x` and
`\max_(x <- xs | P x) F x` are the accepted `sumFiltered`/`maxFiltered`; `a != b` is `decide (a ≠ b)`; `iota a b` is
`List.range' a b`; `muln h` is `fun x => h * x`; `predn` is `Nat.pred`; `ε` is `1`; `[seq A <- s | p A]` is
`s.filter p`; `is_in_search_space` is the accepted `Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space`; `x \in
xs` is `x ∈ xs`; the section's variables and hypotheses are explicit binders, in the order of the elaborated
statement. -/

set_option linter.dupNamespace false

namespace Prosa.Implementation.Refinements.FP.FastSearchSpace

open Prosa.Behavior.Time
open Prosa.Util.Sum
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.NumericFixedPriority
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Implementation.Definitions.Task
open Prosa.Implementation.Refinements.Task
open Prosa.Implementation.Refinements.ArrivalCurve
open Prosa.Implementation.Refinements.FastSearchSpaceComputation

/-- Higher-or-equal priority and a different task. -/
def ohep_task (tsk1 : Task) (tsk2 : Task) : Bool :=
  (NumericFPAscending Task).hep_task tsk1 tsk2 && decide (tsk1 ≠ tsk2)

/-- Total request-bound function of the higher-or-equal-priority tasks. -/
def total_hep_rbf (ts : List Task) (tsk : Task) (Δ : duration) : Nat :=
  @total_hep_request_bound_function_FP Task _ _ _ ts (NumericFPAscending Task) tsk Δ

/-- Total request-bound function of the other higher-or-equal-priority tasks. -/
def total_ohep_rbf (ts : List Task) (tsk : Task) (Δ : duration) : Nat :=
  @total_ohep_request_bound_function_FP Task _ _ _ ts (NumericFPAscending Task) tsk Δ

/-- Check of a point `(A, F)` of the search space under the fully-preemptive policy. -/
def check_point_FP (ts : List Task) (tsk : Task) (R : Nat) (P : Nat × Nat) : Bool :=
  decide (task_rbf tsk (P.1 + 1) + total_ohep_rbf ts tsk (P.1 + P.2) ≤ P.1 + P.2) && decide (P.2 ≤ R)

/-- The blocking bound under nonpreemptive policies. -/
def blocking_bound_NP (ts : List Task) (tsk : Task) : Nat :=
  maxFiltered ts (fun tsk_other => !(NumericFPAscending Task).hep_task tsk_other tsk)
    (fun tsk_other => task_cost tsk_other - 1)

/-- Check of a point `(A, F)` of the search space under the fully-nonpreemptive policy. -/
def check_point_NP (ts : List Task) (tsk : Task) (R : Nat) (P : Nat × Nat) : Bool :=
  decide (blocking_bound_NP ts tsk + (task_rbf tsk (P.1 + 1) - (task_cost tsk - 1)) +
      total_ohep_rbf ts tsk (P.1 + P.2) ≤ P.1 + P.2) &&
    decide (P.2 + (task_cost tsk - 1) ≤ R)

/-- Abstract RTA's search space. -/
def correct_search_space (tsk : Task) (L : duration) : List Nat :=
  (List.range' 0 L).filter (fun A => Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space tsk L A)

/-- The computation-oriented search space in `[a * h, b * h)`. -/
def search_space_emax_FP_h (tsk : Task) (a b : Nat) : List Nat :=
  let h := get_horizon_of_task tsk
  let offsets := (List.range' a b).map (fun x => h * x)
  let emax_offsets := repeat_steps_with_offset tsk offsets
  emax_offsets.map Nat.pred

/-- The computation-oriented search space. -/
def search_space_emax_FP (tsk : Task) (L : duration) : List Nat :=
  let h := get_horizon_of_task tsk
  search_space_emax_FP_h tsk 0 (L / h + 1)

/-- Abstract RTA's search space is a subset of the computation-oriented one. -/
theorem search_space_subset_FP :
    ∀ (L : duration) (ts : List Task), task_set_with_valid_arrivals ts → ∀ tsk : Task, 0 < task_cost tsk →
      tsk ∈ ts → ∀ A : Nat, A ∈ correct_search_space tsk L → A ∈ search_space_emax_FP tsk L := by
  intro L ts hvalid tsk hcost hin A hA
  have hf := (List.mem_filter.mp hA).2
  simp only [Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space, Bool.and_eq_true] at hf
  exact task_search_space_subset L ts hvalid tsk hcost hin A (of_decide_eq_true hf.1) hf.2

end Prosa.Implementation.Refinements.FP.FastSearchSpace
