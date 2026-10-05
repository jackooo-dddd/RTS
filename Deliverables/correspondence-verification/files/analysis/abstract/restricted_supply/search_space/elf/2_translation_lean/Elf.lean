-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/restricted_supply/search_space/elf.v

import Prosa.Analysis.Facts.Model.Rbf
import Prosa.Analysis.Abstract.SearchSpace
import Prosa.Analysis.Definitions.BlockingBound.Elf
import Prosa.Analysis.Facts.Workload.ElfAthepBound

namespace Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Elf

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Model.Task.Preemption.Parameters
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.Gel
open Prosa.Util.Sum
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Elf
open Prosa.Analysis.Definitions.Workload.ElfAthepBound
open Prosa.Analysis.Facts.Model.Rbf

/-! The abstract search space is a subset of the restricted-supply ELF search
space. Binders follow the elaborated source types (unused section context and
hypotheses are absent, as in the elaborated source); the FP policy is the
instance binder of the accepted ELF blocking bound and workload bounds.
Representation: `ε` is `1`; the section-local `task_rbf`,
`task_rbf_changes_at`, `bound_on_ep_task_workload_changes_at` (including its
local `let`), `blocking_bound_changes_at` and `intra_IBF` are inlined;
`a != b` is `decide (a ≠ b)`; `has p xs` is `xs.any p`; `x \in xs` in `Prop`
position is `decide (x ∈ xs) = true`; `search_space.is_in_search_space` is the
accepted abstract search-space predicate. -/

/-- The ELF search space: offsets below `L` where the blocking bound, the RBF
of `tsk` or the bound on the equal-priority workload changes. -/
def is_in_search_space {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskMaxNonpreemptiveSegment Task] [PriorityPoint Task] (ts : List Task) [MaxArrivals Task]
    [FP : FP_policy Task] (tsk : Task) (L A : duration) : Bool :=
  decide (A < L) &&
    ((decide (blocking_bound ts (FP := FP) tsk (A - 1) ≠ blocking_bound ts (FP := FP) tsk A) ||
        decide (task_request_bound_function tsk A ≠ task_request_bound_function tsk (A + 1))) ||
      ts.any (fun tsko => ep_task (FP := FP) tsk tsko && decide (tsko ≠ tsk) &&
        decide (ep_task_interfering_interval_length tsk tsko (A - 1) ≠
          ep_task_interfering_interval_length tsk tsko A)))

theorem search_space_sub {Task : TaskType} [DecidableEq Task] [TaskCost Task]
    [TaskMaxNonpreemptiveSegment Task] [PriorityPoint Task] (ts : List Task) [MaxArrivals Task] :
    valid_taskset_arrival_curve ts max_arrivals →
      ∀ (FP : FP_policy Task) (tsk : Task), decide (tsk ∈ ts) = true →
        ∀ L : duration, 0 < L → 0 < task_cost tsk → 0 < max_arrivals tsk 1 →
          ∀ A : Nat,
            Prosa.Analysis.Abstract.SearchSpace.is_in_search_space L
                (fun A0 F : duration =>
                  task_request_bound_function tsk (A0 + 1) - task_cost tsk +
                    (blocking_bound ts (FP := FP) tsk A0 + bound_on_athep_workload ts (FP := FP) tsk A0 F)) A →
              is_in_search_space ts (FP := FP) tsk L A = true := by
  intro hv FP tsk hin L hL hc hpos A h
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
        (blocking_bound ts (FP := FP) tsk (A - 1) + bound_on_athep_workload ts (FP := FP) tsk (A - 1) x) =
      task_request_bound_function tsk (A + 1) - task_cost tsk +
        (blocking_bound ts (FP := FP) tsk A + bound_on_athep_workload ts (FP := FP) tsk A x)
    rw [hA1, hrbf, hbb]
    congr 2
    unfold bound_on_athep_workload
    congr 1
    unfold bound_on_ep_task_workload
    apply eq_sum_seq
    intro tsko hin' hP
    apply decide_eq_true
    have heq : ep_task_interfering_interval_length tsk tsko (A - 1) =
        ep_task_interfering_interval_length tsk tsko A := by
      by_contra hd
      apply hany
      rw [List.any_eq_true]
      refine ⟨tsko, hin', ?_⟩
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hP ⊢
      exact ⟨hP, hd⟩
    rw [heq]

end Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Elf
