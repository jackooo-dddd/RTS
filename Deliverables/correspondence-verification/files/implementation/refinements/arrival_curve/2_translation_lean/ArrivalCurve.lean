-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/arrival_curve.v

import Prosa.Implementation.Refinements.Task
import Prosa.Analysis.Definitions.RequestBoundFunction

/-! # Arrival curves of concrete tasks, and their refinements

Definitions on the arrival curves of concrete tasks, and refinements relating them, at the binary numbers `N`, to
the generic definitions.

Representation (as in `Refinements`): Rocq cumulativity `Prop ≤ Type` is `PLift`; the source's `Type`-valued
`Global Instance`s are Lean definitions (its `Local Instance`s are not public declarations); the instance
`ConcreteMaxArrivals` applied to a task is its field `max_arrivals`; `sorted` is the accepted `sortedBool`; a Boolean
in `Prop` is `= true`; `x \in xs` is `x ∈ xs`; `p >= 1` is `decide (1 ≤ p)`. -/

set_option linter.dupNamespace false
set_option warn.classDefReducibility false

namespace Prosa.Implementation.Refinements.ArrivalCurve

open Prosa.Behavior.Time
open Prosa.Implementation.Refinements.Refinements
open Prosa.Implementation.Refinements.ArrivalBound
open Prosa.Implementation.Refinements.Task
open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
open Prosa.Implementation.Definitions.ArrivalBound
open Prosa.Implementation.Definitions.Task
open Prosa.Analysis.Definitions.RequestBoundFunction

/-- The horizon of the arrival-curve prefix of a task. -/
def get_horizon_of_task (tsk : Task) : duration := horizon_of (get_arrival_curve_prefix tsk)

/-- The time steps of the arrival-curve prefix of a task. -/
def get_time_steps_of_task (tsk : Task) : List duration := time_steps_of (get_arrival_curve_prefix tsk)

/-- The time steps shifted by an offset. -/
def time_steps_with_offset (tsk : Task) (δ : Nat) : List Nat := (get_time_steps_of_task tsk).map (fun t => t + δ)

/-- The time steps repeated for each offset. -/
def repeat_steps_with_offset (tsk : Task) (offsets : List Nat) : List Nat :=
  (offsets.map (time_steps_with_offset tsk)).flatten

/-- The request-bound function of a task. -/
def task_rbf (tsk : Task) (Δ : duration) : Nat := task_request_bound_function tsk Δ

/-- A valid arrival bound. -/
def valid_arrivals (tsk : Task) : Bool :=
  match concrete_task.task_arrival tsk with
  | .Periodic p => decide (1 ≤ p)
  | .Sporadic m => decide (1 ≤ m)
  | .ArrivalPrefix emax_vec => valid_arrival_curve_prefix_dec emax_vec

/-- The task is periodic. -/
def is_periodic_arrivals (tsk : Task) : Prop := ∃ p, concrete_task.task_arrival tsk = .Periodic p

/-- The task is sporadic. -/
def is_sporadic_arrivals (tsk : Task) : Prop := ∃ m, concrete_task.task_arrival tsk = .Sporadic m

/-- The task is bounded by an arrival-curve prefix. -/
def is_etamax_arrivals (tsk : Task) : Prop :=
  ∃ ac_prefix_vec, concrete_task.task_arrival tsk = .ArrivalPrefix ac_prefix_vec

/-- The task has a valid arrival curve. -/
def has_valid_arrival_curve_prefix (tsk : Task) : Prop :=
  ∃ ac_prefix_vec, get_arrival_curve_prefix tsk = ac_prefix_vec ∧ valid_arrival_curve_prefix ac_prefix_vec

/-- A task set with valid arrivals. -/
def task_set_with_valid_arrivals (ts : List Task) : Prop := ∀ tsk, tsk ∈ ts → valid_arrivals tsk = true

/-- A task is periodic, sporadic, or bounded by an arrival-curve prefix. -/
theorem arrival_cases : ∀ tsk : Task,
    is_periodic_arrivals tsk ∨ is_sporadic_arrivals tsk ∨ is_etamax_arrivals tsk := by
  intro tsk
  cases h : concrete_task.task_arrival tsk with
  | Periodic p => exact Or.inl ⟨p, h⟩
  | Sporadic m => exact Or.inr (Or.inl ⟨m, h⟩)
  | ArrivalPrefix e => exact Or.inr (Or.inr ⟨e, h⟩)

/-! ### Refinements -/

private def steps_R : ∀ st : List (N × N), list_R (prod_R Rnat Rnat) (m_tb2tn st) st
  | [] => .nil_R
  | (_, _) :: st => .cons_R (.pair_R (Rnat_intro rfl) (Rnat_intro rfl)) (steps_R st)

private def prefix_R (e : N × List (N × N)) :
    prod_R Rnat (list_R (prod_R Rnat Rnat)) (ACPrefixT_to_ACPrefix e) e :=
  match e with
  | (_, st) => .pair_R (Rnat_intro rfl) (steps_R st)

private theorem prefix_of_taskT (tsk : task_T N) :
    get_arrival_curve_prefix (taskT_to_task tsk) = ACPrefixT_to_ACPrefix (get_extrapolated_arrival_curve_T tsk) := by
  obtain ⟨id, c, ab, d, pr⟩ := tsk
  cases ab <;> rfl

private def list_R_Rnat_of_map' : ∀ {xs : List Nat} {ys : List N}, xs = ys.map nat_of_bin → list_R Rnat xs ys
  | _, ys, h => h ▸ list_R_Rnat_of_eq ys

private theorem time_steps_of_ACP (e : N × List (N × N)) :
    time_steps_of (ACPrefixT_to_ACPrefix e) = (time_steps_of_T e).map nat_of_bin := by
  obtain ⟨h, st⟩ := e
  simp only [time_steps_of, steps_of, ACPrefixT_to_ACPrefix, steps_of_T, time_steps_of_T, m_tb2tn, tb2tn, tmap,
    List.map_map]
  rfl

private theorem value_at_ACP (e : N × List (N × N)) (u : N) :
    value_at (ACPrefixT_to_ACPrefix e) (nat_of_bin u) = nat_of_bin (value_at_T e u) :=
  (Rnat_eq (refine_value_at.refines_rel _ _ (prefix_R e) _ u (Rnat_intro rfl))).symm

private theorem valid_prefix_eq (e : N × List (N × N)) :
    valid_arrival_curve_prefix_dec (ACPrefixT_to_ACPrefix e) = valid_extrapolated_arrival_curve_T e := by
  have hsort : sorted_ltn_steps (ACPrefixT_to_ACPrefix e) = sorted_ltn_steps_T e := by
    obtain ⟨h, st⟩ := e
    exact bool_R_eq (refine_ltn_steps_sorted _ _ ⟨steps_R st⟩).refines_rel
  have hpos : positive_horizon (ACPrefixT_to_ACPrefix e) = positive_horizon_T e := by
    obtain ⟨h, st⟩ := e
    simp only [positive_horizon, positive_horizon_T, lt_op_N, nat_of_bin_zero, horizon_of, horizon_of_T,
      ACPrefixT_to_ACPrefix]
    exact decide_eq_decide.mpr Iff.rfl
  have hlarge : large_horizon_dec (ACPrefixT_to_ACPrefix e) = large_horizon_T e := by
    simp only [large_horizon_dec, large_horizon_T, time_steps_of_ACP, List.all_map, leq_op_N]
    obtain ⟨h, st⟩ := e
    rfl
  have hnoinf : no_inf_arrivals (ACPrefixT_to_ACPrefix e) = no_inf_arrivals_T e := by
    simp only [no_inf_arrivals, no_inf_arrivals_T, eq_op_N, nat_of_bin_zero]
    rw [← value_at_ACP e zero_op]; rfl
  have hburst : specified_bursts (ACPrefixT_to_ACPrefix e) = specified_bursts_T e := by
    simp only [specified_bursts, specified_bursts_T, time_steps_of_ACP, eq_op_N, nat_of_bin_one]
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, List.mem_map, List.any_eq_true]
    constructor
    · rintro ⟨a, ha, h1⟩; exact ⟨a, ha, decide_eq_true h1⟩
    · rintro ⟨a, ha, h1⟩; exact ⟨a, ha, of_decide_eq_true h1⟩
  simp only [valid_arrival_curve_prefix_dec, valid_extrapolated_arrival_curve_T, hpos, hlarge, hnoinf, hburst, hsort]

/-- Refinement of `valid_arrivals`. -/
def refine_valid_arrivals :
    ∀ tsk : task_T N, refines bool_R (valid_arrivals (taskT_to_task tsk)) (valid_arrivals_T tsk) :=
  fun tsk => ⟨bool_R_of_eq (by
    obtain ⟨id, c, ab, d, pr⟩ := tsk
    cases ab with
    | Periodic_T p =>
      simp only [valid_arrivals, valid_arrivals_T, taskT_to_task, task_abT_to_task_ab, leq_op_N]; rfl
    | Sporadic_T m =>
      simp only [valid_arrivals, valid_arrivals_T, taskT_to_task, task_abT_to_task_ab, leq_op_N]; rfl
    | ArrivalPrefix_T e =>
      simp only [valid_arrivals, valid_arrivals_T, taskT_to_task, task_abT_to_task_ab]
      exact valid_prefix_eq e)⟩

private theorem time_steps_taskT (tsk : task_T N) :
    get_time_steps_of_task (taskT_to_task tsk) = (get_time_steps_of_task_T tsk).map nat_of_bin := by
  simp only [get_time_steps_of_task, get_time_steps_of_task_T, prefix_of_taskT, time_steps_of_ACP]

private theorem time_steps_with_offset_taskT (tsk : task_T N) (o : N) :
    time_steps_with_offset (taskT_to_task tsk) (nat_of_bin o) = (time_steps_with_offset_T tsk o).map nat_of_bin := by
  simp only [time_steps_with_offset, time_steps_with_offset_T, time_steps_taskT, List.map_map]
  apply List.map_congr_left
  intro t _
  simp only [Function.comp, nat_of_bin_add_op]

private theorem repeat_steps_taskT (tsk : task_T N) (os : List N) :
    repeat_steps_with_offset (taskT_to_task tsk) (os.map nat_of_bin) =
      (repeat_steps_with_offset_T tsk os).map nat_of_bin := by
  simp only [repeat_steps_with_offset, repeat_steps_with_offset_T, List.map_map, List.map_flatten]
  congr 1
  apply List.map_congr_left
  intro o _
  exact time_steps_with_offset_taskT tsk o

/-- Refinement of `repeat_steps_with_offset`. -/
def refine_repeat_steps_with_offset :
    refines (hrespectful Rtask (hrespectful (list_R Rnat) (list_R Rnat)))
      repeat_steps_with_offset repeat_steps_with_offset_T :=
  ⟨fun _ tsk' Rt _ os' Ros => list_R_Rnat_of_map' (by
    rw [← Rt.down, ← list_R_Rnat_eq Ros, repeat_steps_taskT])⟩

/-- Refinement of `get_horizon_of_task`. -/
def refine_get_horizon_of_task : refines (hrespectful Rtask Rnat) get_horizon_of_task get_horizon_of_task_T :=
  ⟨fun _ tsk' Rt => Rnat_intro (by
    rw [← Rt.down]
    simp only [get_horizon_of_task, get_horizon_of_task_T, prefix_of_taskT, horizon_of, ACPrefixT_to_ACPrefix])⟩

/-- Refinement of the arrival bound of a converted task. -/
def refine_ConcreteMaxArrivals' :
    ∀ tsk : task_T N,
      refines (hrespectful Rnat Rnat) (ConcreteMaxArrivals.max_arrivals (taskT_to_task tsk)) (ConcreteMaxArrivals_T tsk) :=
  fun tsk => ⟨fun δ δ' Rδ => by
    have h := refine_arrival_curve_prefix.refines_rel _ _ (prefix_R (get_extrapolated_arrival_curve_T tsk)) δ δ' Rδ
    show Rnat (concrete_max_arrivals (taskT_to_task tsk) δ) _
    simp only [concrete_max_arrivals, prefix_of_taskT]
    exact h⟩

/-- Refinement of `get_arrival_curve_prefix`. -/
def refine_get_arrival_curve_prefix :
    refines (hrespectful Rtask (prod_R Rnat (list_R (prod_R Rnat Rnat))))
      get_arrival_curve_prefix get_extrapolated_arrival_curve_T :=
  ⟨fun _ tsk' Rt => by
    rw [← Rt.down, prefix_of_taskT]
    exact prefix_R _⟩

/-- Refinement of `get_arrival_curve_prefix` for a converted task. -/
def refine_get_arrival_curve_prefix' :
    ∀ tsk : task_T N,
      refines (prod_R Rnat (list_R (prod_R Rnat Rnat)))
        (get_arrival_curve_prefix (taskT_to_task tsk)) (get_extrapolated_arrival_curve_T tsk) :=
  fun tsk => ⟨by rw [prefix_of_taskT]; exact prefix_R _⟩

/-- Refinement of `sorted leq_steps` on the steps of a converted task. -/
def refine_sorted_leq_steps :
    ∀ tsk : task_T N,
      refines bool_R (sortedBool leq_steps (steps_of (get_arrival_curve_prefix (taskT_to_task tsk))))
        (sortedBool leq_steps_T (get_extrapolated_arrival_curve_T tsk).2) :=
  fun tsk => by
    rw [prefix_of_taskT]
    obtain ⟨h, st⟩ := get_extrapolated_arrival_curve_T tsk
    exact refine_leq_steps_sorted _ _ ⟨steps_R st⟩

/-- Refinement of the task request-bound function. -/
def refine_task_rbf : refines (hrespectful Rtask (hrespectful Rnat Rnat)) task_rbf task_rbf_T :=
  ⟨fun _ tsk' Rt Δ Δ' RΔ => Rnat_intro (by
    rw [← Rt.down]
    have h := Rnat_eq ((refine_ConcreteMaxArrivals' tsk').refines_rel Δ Δ' RΔ)
    simp only [task_rbf, task_request_bound_function, task_rbf_T]
    show nat_of_bin (N.mul _ _) = _
    rw [nat_of_bin_mul, h]
    obtain ⟨id, c, ab, d, pr⟩ := tsk'
    rfl)⟩

end Prosa.Implementation.Refinements.ArrivalCurve
