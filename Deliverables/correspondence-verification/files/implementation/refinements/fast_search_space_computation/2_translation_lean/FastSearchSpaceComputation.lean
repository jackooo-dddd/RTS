-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/fast_search_space_computation.v

import Prosa.Implementation.Refinements.ArrivalCurvePrefix
import Prosa.Implementation.Facts.ExtrapolatedArrivalCurve
import Prosa.Util.List

/-! # A computation-oriented search space for fixed-priority tasks

Representation (as in `ArrivalCurve`): `iota l r` is `List.range' l r`; `muln h` is `fun x => h * x`; `predn` is
`Nat.pred`; `(L %/ h).+1` is `L / h + 1`; `ε` is `1`; `last0` is the accepted `last0`; `x \in xs` is `x ∈ xs`;
`a != b` (a Boolean in `Prop` position) is `decide (a ≠ b) = true` and `d %| m` is `decide (d ∣ m) = true`; the
section's variables and hypotheses are explicit binders, in the order of the elaborated statements (each statement
takes only those it uses). -/

set_option linter.dupNamespace false

namespace Prosa.Implementation.Refinements.FastSearchSpaceComputation

/-- `omega` after unfolding the time aliases `instant`/`duration` (as in the accepted files). -/
macro "omega'" : tactic => `(tactic| (try dsimp only [instant, duration] at *) <;> omega)

open Prosa.Behavior.Time
open Prosa.Util.List
open Prosa.Implementation.Refinements.ArrivalCurve
open Prosa.Implementation.Refinements.ArrivalCurvePrefix
open Prosa.Implementation.Refinements.Task
open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
open Prosa.Implementation.Facts.ExtrapolatedArrivalCurve
open Prosa.Implementation.Definitions.ArrivalBound
open Prosa.Implementation.Definitions.Task
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Analysis.Definitions.RequestBoundFunction

/-- The search space in the interval `[l * h, r * h)`, by repeating the time steps. -/
def search_space_arrival_curve_prefix_FP_h (tsk : Task) (l r : Nat) : List Nat :=
  let h := get_horizon_of_task tsk
  let offsets := (List.range' l r).map (fun x => h * x)
  let arrival_curve_prefix_offsets := repeat_steps_with_offset tsk offsets
  arrival_curve_prefix_offsets.map Nat.pred

/-- The search space for fixed-priority tasks. -/
def search_space_arrival_curve_prefix_FP (tsk : Task) (L : Nat) : List Nat :=
  let h := get_horizon_of_task tsk
  search_space_arrival_curve_prefix_FP_h tsk 0 (L / h + 1)

/-! ### Local helpers (not source declarations) -/

private theorem mem_search_space (tsk : Task) (L A k t : Nat)
    (hk : k < L / get_horizon_of_task tsk + 1) (ht : t ∈ get_time_steps_of_task tsk)
    (he : A + 1 = t + get_horizon_of_task tsk * k) :
    A ∈ search_space_arrival_curve_prefix_FP tsk L := by
  simp only [search_space_arrival_curve_prefix_FP, search_space_arrival_curve_prefix_FP_h,
    repeat_steps_with_offset]
  refine List.mem_map.mpr ⟨A + 1, ?_, rfl⟩
  refine List.mem_flatten.mpr ⟨(get_time_steps_of_task tsk).map (fun x => x + get_horizon_of_task tsk * k), ?_, ?_⟩
  · refine List.mem_map.mpr ⟨get_horizon_of_task tsk * k, ?_, rfl⟩
    exact List.mem_map.mpr ⟨k, List.mem_range'_1.mpr ⟨Nat.zero_le _, by omega'⟩, rfl⟩
  · exact List.mem_map.mpr ⟨t, ht, he.symm⟩

private theorem le_last_of_sorted :
    ∀ (a : Nat) (xs : List Nat), sortedBoolFrom (fun x y => decide (x < y)) a xs = true →
      ∀ s ∈ a :: xs, s ≤ (a :: xs).getLastD 0
  | a, [], _, s, hs => by
      simp only [List.mem_singleton] at hs
      subst hs; simp
  | a, b :: xs, h, s, hs => by
      simp only [sortedBoolFrom, Bool.and_eq_true, decide_eq_true_eq] at h
      have ih := le_last_of_sorted b xs h.2
      have hlast : (a :: b :: xs).getLastD 0 = (b :: xs).getLastD 0 := by simp [List.getLastD]
      rw [hlast]
      rcases List.mem_cons.mp hs with rfl | hs
      · exact Nat.le_trans (Nat.le_of_lt h.1) (ih b (List.mem_cons_self))
      · exact ih s hs

private theorem last0_mem : ∀ (a : Nat) (xs : List Nat), last0 (a :: xs) ∈ a :: xs
  | a, [] => by simp [last0, List.getLastD]
  | a, b :: xs => by
      have : last0 (a :: b :: xs) = last0 (b :: xs) := by simp [last0, List.getLastD]
      rw [this]
      exact List.mem_cons_of_mem a (last0_mem b xs)

private theorem steps_le_last0 (xs : List Nat) (hs : sortedBool (fun x y => decide (x < y)) xs = true) :
    ∀ s ∈ xs, s ≤ last0 xs := by
  cases xs with
  | nil => intro s h; simp at h
  | cons a xs => exact le_last_of_sorted a xs hs

/-- Validity of the prefix of a task of a valid task set, unpacked. -/
private theorem valid_prefix (ts : List Task) (hvalid : task_set_with_valid_arrivals ts) (tsk : Task)
    (hin : tsk ∈ ts) :
    positive_horizon (get_arrival_curve_prefix tsk) = true ∧
      large_horizon (get_arrival_curve_prefix tsk) ∧
      no_inf_arrivals (get_arrival_curve_prefix tsk) = true ∧
      specified_bursts (get_arrival_curve_prefix tsk) = true ∧
      sorted_ltn_steps (get_arrival_curve_prefix tsk) = true := by
  obtain ⟨ac, hac, hv⟩ := has_valid_arrival_curve_prefix_tsk ts hvalid tsk hin
  rw [hac]; exact hv

private theorem succ_div_cases (A h : Nat) :
    (A + 1) / h = A / h + (if h ∣ A + 1 then 1 else 0) := Nat.succ_div

/-- The quotients and remainders of `A` and `A + 1` when `h` divides `A + 1`. -/
private theorem div_mod_of_dvd_succ (A h k : Nat) (hpos : 0 < h) (hk : A + 1 = h * (k + 1)) :
    A / h = k ∧ A % h = h - 1 ∧ (A + 1) / h = k + 1 ∧ (A + 1) % h = 0 := by
  have hA : A = (h - 1) + h * k := by
    rw [Nat.mul_succ] at hk
    generalize h * k = m at hk ⊢
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hA, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (by omega)]; simp
  · rw [hA, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · rw [hk, Nat.mul_div_cancel_left _ hpos]
  · rw [hk, Nat.mul_mod_right]

/-! ### Statements -/

/-- Each time step is below the horizon, or the last time step is the horizon. -/
theorem steps_lt_horizon_last_eq_horizon :
    ∀ ts : List Task, task_set_with_valid_arrivals ts → ∀ tsk : Task, 0 < task_cost tsk → tsk ∈ ts →
      (∀ s : Nat, s ∈ get_time_steps_of_task tsk → s < get_horizon_of_task tsk) ∨
        last0 (get_time_steps_of_task tsk) = get_horizon_of_task tsk := by
  intro ts hvalid tsk _ hin
  obtain ⟨_, hlarge, _, _, _⟩ := valid_prefix ts hvalid tsk hin
  have hle : ∀ s ∈ get_time_steps_of_task tsk, s ≤ get_horizon_of_task tsk := fun s hs => hlarge s hs
  have hsorted := time_steps_sorted ts hvalid tsk hin
  by_cases heq : last0 (get_time_steps_of_task tsk) = get_horizon_of_task tsk
  · exact Or.inr heq
  · left
    intro s hs
    have hsl := steps_le_last0 _ hsorted s hs
    cases hxs : get_time_steps_of_task tsk with
    | nil => rw [hxs] at hs; simp at hs
    | cons a xs =>
        have hmem : last0 (get_time_steps_of_task tsk) ∈ get_time_steps_of_task tsk := by
          rw [hxs]; exact last0_mem a xs
        have hlh := hle _ hmem
        exact Nat.lt_of_le_of_lt hsl (Nat.lt_of_le_of_ne hlh heq)

/-- A change of the request-bound function is a step of the prefix offset by a multiple of the horizon, or a
multiple of the horizon. -/
theorem structure_of_correct_search_space :
    ∀ (L : duration) (ts : List Task), task_set_with_valid_arrivals ts → ∀ tsk : Task, 0 < task_cost tsk →
      tsk ∈ ts → ∀ A : Nat, A < L → decide (task_rbf tsk A ≠ task_rbf tsk (A + 1)) = true →
        (∃ (i : Nat) (t : Nat), i < L / get_horizon_of_task tsk + 1 ∧ t ∈ get_time_steps_of_task tsk ∧
            A + 1 = i * get_horizon_of_task tsk + t) ∨
          (∃ i : Nat, i < L / get_horizon_of_task tsk + 1 ∧ A + 1 = i * get_horizon_of_task tsk) := by
  intro L ts hvalid tsk hcost hin A hlt hneq
  obtain ⟨hpos, _, hnoinf, _, hsort⟩ := valid_prefix ts hvalid tsk hin
  have hsortleq := sorted_ltn_steps_imply_sorted_leq_steps_steps _ hsort hnoinf
  have hneq' : extrapolated_arrival_curve (get_arrival_curve_prefix tsk) A ≠
      extrapolated_arrival_curve (get_arrival_curve_prefix tsk) (A + 1) := by
    intro he
    apply of_decide_eq_true hneq
    show task_cost tsk * concrete_max_arrivals tsk A = task_cost tsk * concrete_max_arrivals tsk (A + 1)
    simp only [concrete_max_arrivals, he]
  have hh : get_horizon_of_task tsk = horizon_of (get_arrival_curve_prefix tsk) := rfl
  have hpos' : 0 < horizon_of (get_arrival_curve_prefix tsk) := of_decide_eq_true hpos
  have hi : (A + 1) / get_horizon_of_task tsk < L / get_horizon_of_task tsk + 1 :=
    Nat.lt_succ_of_le (Nat.div_le_div_right (by omega'))
  rcases extrapolated_arrival_curve_change _ hpos hsortleq A hneq' with hlt' | ⟨heqd, hval⟩
  · right
    refine ⟨(A + 1) / get_horizon_of_task tsk, hi, ?_⟩
    have hd : get_horizon_of_task tsk ∣ A + 1 := by
      rw [← hh] at hlt'
      have := succ_div_cases A (get_horizon_of_task tsk)
      by_cases hdv : get_horizon_of_task tsk ∣ A + 1
      · exact hdv
      · rw [if_neg hdv] at this; omega'
    exact (Nat.div_mul_cancel hd).symm
  · left
    rw [← hh] at heqd hval
    have hnd : ¬ get_horizon_of_task tsk ∣ A + 1 := by
      intro hdv
      have := succ_div_cases A (get_horizon_of_task tsk)
      rw [if_pos hdv] at this; omega'
    have e1 := Nat.div_add_mod A (get_horizon_of_task tsk)
    have e2 := Nat.div_add_mod (A + 1) (get_horizon_of_task tsk)
    have hmod : (A + 1) % get_horizon_of_task tsk = A % get_horizon_of_task tsk + 1 := by
      rw [← heqd] at e2
      generalize get_horizon_of_task tsk * (A / get_horizon_of_task tsk) = m at e1 e2
      omega'
    rw [hmod] at hval
    obtain ⟨v, hv⟩ := value_at_change_is_in_steps_of _ hsortleq hnoinf _ hval
    refine ⟨(A + 1) / get_horizon_of_task tsk, (A + 1) % get_horizon_of_task tsk, hi, ?_, ?_⟩
    · rw [hmod]
      exact List.mem_map.mpr ⟨_, hv, rfl⟩
    · rw [Nat.mul_comm]; exact e2.symm

/-- Every multiple of the horizon below `L` is in the search space. -/
theorem multiple_of_horizon_in_approx_ss :
    ∀ (L : duration) (ts : List Task), task_set_with_valid_arrivals ts → ∀ tsk : Task, 0 < task_cost tsk →
      tsk ∈ ts → ∀ A : Nat, A < L → decide (get_horizon_of_task tsk ∣ A) = true →
        A ∈ search_space_arrival_curve_prefix_FP tsk L := by
  intro L ts hvalid tsk _ hin A hlt hdiv
  obtain ⟨hpos, _, _, hburst, _⟩ := valid_prefix ts hvalid tsk hin
  have hpos' : 0 < get_horizon_of_task tsk := of_decide_eq_true hpos
  obtain ⟨k, hk⟩ := of_decide_eq_true hdiv
  refine mem_search_space tsk L A k 1 ?_ (of_decide_eq_true hburst) (by omega')
  have : k ≤ L / get_horizon_of_task tsk := by
    rw [Nat.le_div_iff_mul_le hpos', Nat.mul_comm]; omega'
  omega'

/-- Every step offset by a multiple of the horizon below `L` is in the search space. -/
theorem steps_in_approx_ss :
    ∀ (L : duration) (ts : List Task), task_set_with_valid_arrivals ts → ∀ tsk : Task, 0 < task_cost tsk →
      tsk ∈ ts → ∀ (i : Nat) (t : Nat) (A : Nat), i < L / get_horizon_of_task tsk + 1 →
        t ∈ get_time_steps_of_task tsk → A + 1 = i * get_horizon_of_task tsk + t →
          A ∈ search_space_arrival_curve_prefix_FP tsk L := by
  intro L ts _ tsk _ _ i t A hi ht he
  exact mem_search_space tsk L A i t hi ht (by rw [he, Nat.mul_comm]; omega')

/-- If every step is below the horizon and the horizon divides `A + 1`, the arrival bound does not change at `A`. -/
theorem constant_max_arrivals :
    ∀ ts : List Task, task_set_with_valid_arrivals ts → ∀ tsk : Task, 0 < task_cost tsk → tsk ∈ ts →
      ∀ A : Nat, (∀ s : Nat, s ∈ get_time_steps_of_task tsk → s < get_horizon_of_task tsk) →
        decide (get_horizon_of_task tsk ∣ A + 1) = true → max_arrivals tsk A = max_arrivals tsk (A + 1) := by
  intro ts hvalid tsk _ hin A hlth hdiv
  obtain ⟨hpos, _, hnoinf, hburst, _⟩ := valid_prefix ts hvalid tsk hin
  show A / get_horizon_of_task tsk * value_at (get_arrival_curve_prefix tsk) (get_horizon_of_task tsk) +
      value_at (get_arrival_curve_prefix tsk) (A % get_horizon_of_task tsk) =
    (A + 1) / get_horizon_of_task tsk * value_at (get_arrival_curve_prefix tsk) (get_horizon_of_task tsk) +
      value_at (get_arrival_curve_prefix tsk) ((A + 1) % get_horizon_of_task tsk)
  have hpos' : 0 < get_horizon_of_task tsk := of_decide_eq_true hpos
  have h1 : 1 < get_horizon_of_task tsk := hlth 1 (of_decide_eq_true hburst)
  have hdvd : get_horizon_of_task tsk ∣ A + 1 := of_decide_eq_true hdiv
  have hzero : value_at (get_arrival_curve_prefix tsk) 0 = 0 := of_decide_eq_true hnoinf
  -- the value is constant from `h - 1` on, since every step is below the horizon
  have hsteps : ∀ s ∈ steps_of (get_arrival_curve_prefix tsk), s.1 < get_horizon_of_task tsk :=
    fun s hs => hlth s.1 (List.mem_map.mpr ⟨s, hs, rfl⟩)
  have hconst : ∀ t : Nat, get_horizon_of_task tsk ≤ t + 1 →
      value_at (get_arrival_curve_prefix tsk) t =
        value_at (get_arrival_curve_prefix tsk) (get_horizon_of_task tsk) := by
    intro t ht
    unfold value_at step_at
    rw [List.filter_eq_self.mpr, List.filter_eq_self.mpr]
    · intro s hs; exact decide_eq_true (Nat.le_of_lt (hsteps s hs))
    · intro s hs; exact decide_eq_true (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (hsteps s hs) ht))
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    rcases k with _ | k'
    · simp at hk
    · exact ⟨k', rfl⟩
  obtain ⟨hdivA, hmodA, hdivA1, hmodA1⟩ := div_mod_of_dvd_succ A (get_horizon_of_task tsk) k' hpos' hk
  rw [hdivA, hmodA, hdivA1, hmodA1,
    hconst (get_horizon_of_task tsk - 1) (Nat.le_of_eq (Nat.sub_add_cancel hpos').symm), hzero, Nat.succ_mul,
    Nat.add_zero]

/-- Every change of the request-bound function below `L` is in the search space. -/
theorem task_search_space_subset :
    ∀ (L : duration) (ts : List Task), task_set_with_valid_arrivals ts → ∀ tsk : Task, 0 < task_cost tsk →
      tsk ∈ ts → ∀ A : Nat, A < L → decide (task_rbf tsk A ≠ task_rbf tsk (A + 1)) = true →
        A ∈ search_space_arrival_curve_prefix_FP tsk L := by
  intro L ts hvalid tsk hcost hin A hlt hneq
  by_cases hdiv : get_horizon_of_task tsk ∣ A
  · exact multiple_of_horizon_in_approx_ss L ts hvalid tsk hcost hin A hlt (decide_eq_true hdiv)
  rcases structure_of_correct_search_space L ts hvalid tsk hcost hin A hlt hneq with
    ⟨i, t, hi, ht, he⟩ | ⟨i, hi, he⟩
  · exact steps_in_approx_ss L ts hvalid tsk hcost hin i t A hi ht he
  rcases steps_lt_horizon_last_eq_horizon ts hvalid tsk hcost hin with hlth | hlast
  · exfalso
    have hc := constant_max_arrivals ts hvalid tsk hcost hin A hlth
      (decide_eq_true ⟨i, by rw [he, Nat.mul_comm]⟩)
    apply of_decide_eq_true hneq
    show task_cost tsk * max_arrivals tsk A = task_cost tsk * max_arrivals tsk (A + 1)
    rw [hc]
  · obtain ⟨_, _, _, hburst, _⟩ := valid_prefix ts hvalid tsk hin
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := by
      rcases i with _ | i'
      · simp at he
      · exact ⟨i', rfl⟩
    have hne : get_time_steps_of_task tsk ≠ [] := by
      intro h; have := of_decide_eq_true hburst
      change 1 ∈ get_time_steps_of_task tsk at this
      rw [h] at this; simp at this
    have hmem : get_horizon_of_task tsk ∈ get_time_steps_of_task tsk := by
      rw [← hlast]
      cases hxs : get_time_steps_of_task tsk with
      | nil => exact absurd hxs hne
      | cons a xs => exact last0_mem a xs
    refine mem_search_space tsk L A i' (get_horizon_of_task tsk) (by omega') hmem ?_
    rw [he, Nat.succ_mul, Nat.mul_comm, Nat.add_comm]

end Prosa.Implementation.Refinements.FastSearchSpaceComputation
