-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/search_space/edf.v

import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Abstract.SearchSpace
import Prosa.Analysis.Definitions.BlockingBound.Edf
import Prosa.Analysis.Facts.Workload.EdfAthepBound

namespace Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Edf
open Prosa.Analysis.Definitions.Workload.EdfAthepBound
open Prosa.Analysis.Facts.Model.Rbf

/-! The abstract search space is a subset of the restricted-supply EDF search
space. Binders follow the elaborated source types (unused section context and
hypotheses are absent, as in the elaborated source). Representation: `ε` is
`1`; the section-local `D`, `rbf`, `task_rbf_changes_at`,
`bound_on_total_hep_workload_changes_at` (including its local `let`),
`blocking_bound_changes_at` and `intra_IBF` are inlined; `a != b` is
`decide (a ≠ b)`; `has p xs` is `xs.any p`; `x \in xs` in `Prop` position is
`decide (x ∈ xs) = true`; `search_space.is_in_search_space` is the accepted
abstract search-space predicate. -/

/-- The EDF search space: offsets below `L` where the blocking bound, the RBF
of `tsk` or the bound on the higher-or-equal-priority workload changes. -/
def is_in_search_space {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskDeadline Task]
    [TaskMaxNonpreemptiveSegment Task] (ts : List Task) [MaxArrivals Task]
    (tsk : Task) (L A : duration) : Bool :=
  decide (A < L) &&
    ((decide (blocking_bound ts tsk (A - 1) ≠ blocking_bound ts tsk A) ||
        decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + 1))) ||
      ts.any (fun tsko => decide (tsk ≠ tsko) &&
        decide (task_request_bound_function tsko (A + task_deadline tsk - task_deadline tsko) ≠
          task_request_bound_function tsko (A + 1 + task_deadline tsk - task_deadline tsko))))

theorem search_space_sub {Task : TaskType} [DecidableEq Task] [TaskCost Task] [TaskDeadline Task]
    [TaskMaxNonpreemptiveSegment Task] (ts : List Task) [MaxArrivals Task] :
    valid_taskset_arrival_curve ts max_arrivals →
      ∀ tsk : Task, decide (tsk ∈ ts) = true →
        ∀ L : duration, 0 < L → 0 < task_cost tsk → 0 < max_arrivals tsk 1 →
          ∀ A : Nat,
            Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                (fun A0 F : duration =>
                  task_request_bound_function tsk (A0 + 1) - task_cost tsk +
                    (blocking_bound ts tsk A0 + bound_on_athep_workload ts tsk A0 F)) A →
              is_in_search_space ts tsk L A = true := by
  intro hv tsk hin L hL hc hpos A h
  unfold is_in_search_space
  simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  rcases h with hA | ⟨hA0, hAL, x, _, hne⟩
  · subst hA
    have h0 := task_rbf_0_zero tsk (hv tsk hin)
    have h1 := task_rbf_epsilon_gt_0 tsk hc hpos
    refine ⟨hL, Or.inl (Or.inr ?_)⟩
    rw [h0, Nat.zero_add]
    exact Nat.ne_of_lt h1
  · refine ⟨hAL, ?_⟩
    by_contra hcon
    simp only [not_or, not_not] at hcon
    obtain ⟨⟨hbb, hrbf⟩, hany⟩ := hcon
    apply hne
    have hA1 : A - 1 + 1 = A := Nat.sub_add_cancel hA0
    show task_request_bound_function tsk (A - 1 + 1) - task_cost tsk +
        (blocking_bound ts tsk (A - 1) + bound_on_athep_workload ts tsk (A - 1) x) =
      task_request_bound_function tsk (A + 1) - task_cost tsk +
        (blocking_bound ts tsk A + bound_on_athep_workload ts tsk A x)
    rw [hA1, hrbf, hbb]
    congr 2
    unfold bound_on_athep_workload
    apply eq_sum_seq
    intro tsko hin' hneq
    apply decide_eq_true
    have hne' : tsk ≠ tsko := fun e => (of_decide_eq_true hneq) e.symm
    have heq : task_request_bound_function tsko (A + task_deadline tsk - task_deadline tsko) =
        task_request_bound_function tsko (A + 1 + task_deadline tsk - task_deadline tsko) := by
      by_contra hd
      apply hany
      rw [List.any_eq_true]
      exact ⟨tsko, hin', by simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨hne', hd⟩⟩
    rw [hA1]
    by_cases hx1 : x ≤ A + task_deadline tsk - task_deadline tsko
    · rw [Nat.min_eq_right hx1, Nat.min_eq_right (by omega)]
    · by_cases hx2 : A + 1 + task_deadline tsk - task_deadline tsko ≤ x
      · rw [Nat.min_eq_left (by omega), Nat.min_eq_left hx2]
        exact heq
      · exfalso
        omega

end Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf
