-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/EDF/fast_search_space.v

import Prosa.Results.Rta.Ideal.Edf.BoundedNps
import Prosa.Analysis.Definitions.BlockingBound.Edf
import Prosa.Util.Bigcat
import Prosa.Implementation.Refinements.FastSearchSpaceComputation

/-! # A computation-oriented search space for earliest-deadline-first RTA

Representation (as in `ArrivalCurve` and `FastSearchSpaceComputation`): the four definitions before the section are
over the accepted `Prosa.Implementation.Refinements.Task.Task`; the section's own `Task`/`Job` aliases (the concrete
types as `eqType`s) are abbreviations of the accepted concrete types; the section's `#[local] Existing Instance
ConcreteMaxArrivals` is the accepted global instance; the section's `Context TMNSP` is used by no definition, so no
declaration takes it; `\sum_(x <- xs | P x) F x` and `\max_(x <- xs | P x) F x` are the accepted
`sumFiltered`/`maxFiltered`; `\cat_(x <- xs) F x` is the accepted `bigCatSeqAll`; `[seq i | i <- ts]` is
`ts.map (fun i => i)`; `minn` is `min`; `a != b` is `decide (a ≠ b)`; `iota a b` is `List.range' a b`;
`[seq h * i | i <- s]` is `s.map (fun i => h * i)`; `i.-1` is `Nat.pred i`; `ε` is `1`; `[seq A <- s | p A]` is
`s.filter p`; `is_in_search_space` is the accepted `Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space`;
`x \in xs` is `x ∈ xs`; `head (0, 0) s` is `s.headD (0, 0)`; the section's variables and hypotheses are explicit
binders, in the order of the elaborated statements. -/

set_option linter.dupNamespace false

namespace Prosa.Implementation.Refinements.EDF.FastSearchSpace

open Prosa.Behavior.Time
open Prosa.Util.Sum
open Prosa.Util.List
open Prosa.Util.Bigcat
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Edf
open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
open Prosa.Implementation.Definitions.Task
open Prosa.Implementation.Refinements.ArrivalCurve
open Prosa.Implementation.Refinements.ArrivalCurvePrefix
open Prosa.Implementation.Refinements.FastSearchSpaceComputation

/-- `omega` after unfolding the time aliases `instant`/`duration` (as in the accepted files). -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

/-- The bound on the total higher-or-equal-priority workload. -/
def bound_on_total_hep_workload (ts : List Prosa.Implementation.Refinements.Task.Task)
    (tsk : Prosa.Implementation.Refinements.Task.Task) (A Δ : Nat) : Nat :=
  sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk))
    (fun tsk_o => task_rbf tsk_o (min (A + 1 + task_deadline tsk - task_deadline tsk_o) Δ))

/-- Check of a point `(A, F)` of the search space under the fully-preemptive policy. -/
def check_point_FP (ts : List Prosa.Implementation.Refinements.Task.Task)
    (tsk : Prosa.Implementation.Refinements.Task.Task) (R : Nat) (P : Nat × Nat) : Bool :=
  decide (task_rbf tsk (P.1 + 1) + bound_on_total_hep_workload ts tsk P.1 (P.1 + P.2) ≤ P.1 + P.2) &&
    decide (P.2 ≤ R)

/-- The blocking bound under nonpreemptive policies. -/
def blocking_bound_NP (ts : List Prosa.Implementation.Refinements.Task.Task)
    (tsk : Prosa.Implementation.Refinements.Task.Task) (A : Nat) : Nat :=
  maxFiltered (ts.map (fun i => i))
    (fun tsk_o => blocking_relevant tsk_o && decide (task_deadline tsk + A < task_deadline tsk_o))
    (fun tsk_o => task_cost tsk_o - 1)

/-- Check of a point `(A, F)` of the search space under the fully-nonpreemptive policy. -/
def check_point_NP (ts : List Prosa.Implementation.Refinements.Task.Task)
    (tsk : Prosa.Implementation.Refinements.Task.Task) (R : Nat) (P : Nat × Nat) : Bool :=
  decide (blocking_bound_NP ts tsk P.1 + (task_rbf tsk (P.1 + 1) - (task_cost tsk - 1)) +
      bound_on_total_hep_workload ts tsk P.1 (P.1 + P.2) ≤ P.1 + P.2) &&
    decide (P.2 + (task_cost tsk - 1) ≤ R)

/-! ### Search space definitions -/

/-- The concrete task type. -/
abbrev Task : Type := concrete_task

/-- The concrete job type. -/
abbrev Job : Type := concrete_job

/-- Abstract RTA's search space. -/
def correct_search_space (ts : List Task) (tsk : Task) (L : duration) : List duration :=
  (List.range' 0 L).filter (fun A => Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space ts tsk L A)

/-- The fixed-priority search space in `[l * h, r * h)`. -/
def search_space_emax_FP_h (tsk : Task) (l r : Nat) : List Nat :=
  let h := get_horizon_of_task tsk
  let offsets := (List.range' l r).map (fun x => h * x)
  let emax_offsets := repeat_steps_with_offset tsk offsets
  emax_offsets.map Nat.pred

/-- The fixed-priority search space. -/
def search_space_emax_FP (L : Nat) (tsk : Task) : List Nat :=
  let h := get_horizon_of_task tsk
  search_space_emax_FP_h tsk 0 (L / h + 1)

/-- The search space of `tsk` induced by `tsko` in `[l * h, r * h)`. -/
def task_search_space_emax_EDF_h (tsk tsko : Task) (l r : Nat) : List Nat :=
  let h := get_horizon_of_task tsko
  let offsets := (List.range' l r).map (fun i => h * i)
  let emax_offsets := repeat_steps_with_offset tsko offsets
  let emax_edf_offsets := shift_points_neg (shift_points_pos emax_offsets (task_deadline tsko)) (task_deadline tsk)
  emax_edf_offsets.map Nat.pred

/-- The search space of `tsk` induced by `tsko`. -/
def task_search_space_emax_EDF (tsk tsko : Task) (L : Nat) : List Nat :=
  let h := get_horizon_of_task tsko
  task_search_space_emax_EDF_h tsk tsko 0 ((L + (task_deadline tsk - task_deadline tsko)) / h + 1)

/-- The search space: the concatenation of the per-task search spaces. -/
def search_space_emax_EDF (ts : List Task) (tsk : Task) (L : Nat) : List Nat :=
  bigCatSeqAll ts (fun tsko => task_search_space_emax_EDF tsk tsko L)

/-! ### Local helpers (not source declarations) -/

private theorem shift_neg_pos (S : List Nat) (d : Nat) : shift_points_neg (shift_points_pos S d) d = S := by
  induction S with
  | nil => rfl
  | cons x S ih =>
      simp only [shift_points_neg, shift_points_pos] at ih ⊢
      simp only [List.map_cons, List.filter_cons, decide_eq_true (Nat.le_add_right d x), if_true,
        Nat.add_sub_cancel_left, ih]

/-! ### Statements -/

/-- The EDF search space of a task against itself is the fixed-priority search space. -/
theorem EDF_ss_generalize_FP_ss :
    ∀ (L : duration) (ts : List Task) (tsk : Task), tsk ∈ ts →
      task_search_space_emax_EDF_h tsk tsk 0
          ((L + (task_deadline tsk - task_deadline tsk)) / get_horizon_of_task tsk + 1) =
        search_space_emax_FP L tsk := by
  intro L ts tsk _
  simp only [task_search_space_emax_EDF_h, search_space_emax_FP, search_space_emax_FP_h, Nat.sub_self,
    Nat.add_zero, shift_neg_pos]

/-- Abstract RTA's search space is a subset of the computation-oriented one. -/
theorem search_space_subset_EDF :
    ∀ (L : duration) (ts : List Task), task_set_with_valid_arrivals ts →
      (∀ tsk : Task, tsk ∈ ts → 0 < task_cost tsk) →
      (∀ tsk : Task, tsk ∈ ts → 0 < ((steps_of (get_arrival_curve_prefix tsk)).headD (0, 0)).1) →
      ∀ tsk : Task, tsk ∈ ts → ∀ A : Nat, A ∈ correct_search_space ts tsk L → A ∈ search_space_emax_EDF ts tsk L := by
  intro L ts hvalid hcost hstep tsk hin A hA
  obtain ⟨-, hf⟩ := List.mem_filter.mp hA
  simp only [Prosa.Results.Rta.Ideal.Edf.BoundedNps.is_in_search_space, Bool.and_eq_true,
    Bool.or_eq_true] at hf
  obtain ⟨hlt, hch | hch⟩ := hf
  · -- the request-bound function of `tsk` changes: the task's own search space
    refine List.mem_flatMap.mpr ⟨tsk, hin, ?_⟩
    show A ∈ task_search_space_emax_EDF_h tsk tsk 0
      ((L + (task_deadline tsk - task_deadline tsk)) / get_horizon_of_task tsk + 1)
    rw [EDF_ss_generalize_FP_ss L ts tsk hin]
    exact task_search_space_subset L ts hvalid tsk (hcost tsk hin) hin A (of_decide_eq_true hlt) hch
  · -- the bound of another task `tsko` changes
    obtain ⟨tsko, hino, hpair⟩ := List.any_eq_true.mp hch
    simp only [Bool.and_eq_true] at hpair
    obtain ⟨-, hneq⟩ := hpair
    have hneq' := of_decide_eq_true hneq
    refine List.mem_flatMap.mpr ⟨tsko, hino, ?_⟩
    have hlt' : A < L := of_decide_eq_true hlt
    -- the deadline of `tsko` is at most `A + D_tsk`
    have hAD : task_deadline tsko ≤ A + task_deadline tsk := by
      apply Classical.byContradiction
      intro hc
      apply hneq'
      have e1 : A + task_deadline tsk - task_deadline tsko = 0 := by omega'
      have e2 : A + 1 + task_deadline tsk - task_deadline tsko = 0 := by omega'
      rw [e1, e2]
    -- the corresponding change point of `tsko`
    let B := A + task_deadline tsk - task_deadline tsko
    have hB1 : A + 1 + task_deadline tsk - task_deadline tsko = B + 1 := by omega'
    have hBch : decide (task_rbf tsko B ≠ task_rbf tsko (B + 1)) = true := by
      rw [← hB1]; exact hneq
    have hBL : B < L + (task_deadline tsk - task_deadline tsko) := by omega'
    have hBin := task_search_space_subset (L + (task_deadline tsk - task_deadline tsko)) ts hvalid tsko
      (hcost tsko hino) hino B hBL hBch
    simp only [search_space_arrival_curve_prefix_FP, search_space_arrival_curve_prefix_FP_h] at hBin
    obtain ⟨C, hC, hCB⟩ := List.mem_map.mp hBin
    have hCpos : 0 < C := nonshifted_offsets_are_positive ts hvalid tsko (hcost tsko hino) hino (hstep tsko hino) C _ hC
    have hCeq : C = B + 1 := by
      have : Nat.pred C + 1 = C := Nat.succ_pred_eq_of_pos hCpos
      omega'
    show A ∈ task_search_space_emax_EDF_h tsk tsko 0
      ((L + (task_deadline tsk - task_deadline tsko)) / get_horizon_of_task tsko + 1)
    simp only [task_search_space_emax_EDF_h, shift_points_neg, shift_points_pos]
    refine List.mem_map.mpr ⟨A + 1, ?_, rfl⟩
    refine List.mem_map.mpr ⟨task_deadline tsko + C, ?_, by omega'⟩
    refine List.mem_filter.mpr ⟨List.mem_map.mpr ⟨C, hC, rfl⟩, decide_eq_true (by omega')⟩

end Prosa.Implementation.Refinements.EDF.FastSearchSpace
