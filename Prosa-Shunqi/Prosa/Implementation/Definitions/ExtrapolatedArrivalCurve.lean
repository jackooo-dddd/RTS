-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/definitions/extrapolated_arrival_curve.v

import Prosa.Behavior.Time
import Prosa.Util.All

namespace Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve

open Prosa.Behavior.Time

/-- LEAN_HELPER: constructor-preserving counterpart of MathComp `reflect`.
The Boolean index remains observable; this does not erase the informative
source view to an arbitrary proposition. -/
inductive BoolReflect (P : Prop) : Bool → Type where
  | isTrue : P → BoolReflect P true
  | isFalse : (¬ P) → BoolReflect P false

/-- LEAN_HELPER: structurally recursive adjacent-pair Boolean fold. -/
def sortedBoolFrom {α : Type _} (R : α → α → Bool)
    (previous : α) : List α → Bool
  | [] => true
  | next :: rest => R previous next && sortedBoolFrom R next rest

/-- LEAN_HELPER: ordered, adjacent Boolean sortedness. -/
def sortedBool {α : Type _} (R : α → α → Bool) (xs : List α) : Bool :=
  match xs with
  | [] => true
  | first :: rest => sortedBoolFrom R first rest

abbrev ArrivalCurvePrefix : Type := duration × List (duration × Nat)

def inter_arrival_to_prefix (p : Nat) : ArrivalCurvePrefix :=
  (p, [(1, 1)])

def horizon_of (ac_prefix : ArrivalCurvePrefix) : duration :=
  ac_prefix.1

def steps_of (ac_prefix : ArrivalCurvePrefix) : List (duration × Nat) :=
  ac_prefix.2

def time_steps_of (ac_prefix : ArrivalCurvePrefix) : List duration :=
  (steps_of ac_prefix).map Prod.fst

def step_at (ac_prefix : ArrivalCurvePrefix) (t : duration) : duration × Nat :=
  ((steps_of ac_prefix).filter (fun step => decide (step.1 ≤ t))).getLastD (0, 0)

def value_at (ac_prefix : ArrivalCurvePrefix) (t : duration) : Nat :=
  (step_at ac_prefix t).2

def extrapolated_arrival_curve (ac_prefix : ArrivalCurvePrefix)
    (t : duration) : Nat :=
  let h := horizon_of ac_prefix
  t / h * value_at ac_prefix h + value_at ac_prefix (t % h)

def positive_horizon (ac_prefix : ArrivalCurvePrefix) : Bool :=
  decide (0 < horizon_of ac_prefix)

def large_horizon (ac_prefix : ArrivalCurvePrefix) : Prop :=
  ∀ s, s ∈ time_steps_of ac_prefix → s ≤ horizon_of ac_prefix

def large_horizon_dec (ac_prefix : ArrivalCurvePrefix) : Bool :=
  (time_steps_of ac_prefix).all (fun s => decide (s ≤ horizon_of ac_prefix))

/-- LEAN_HELPER: Boolean list universal corresponds to the public predicate. -/
theorem large_horizon_iff (ac_prefix : ArrivalCurvePrefix) :
    large_horizon_dec ac_prefix = true ↔ large_horizon ac_prefix := by
  constructor
  · intro hd s hs
    have hall : ∀ x ∈ time_steps_of ac_prefix,
        decide (x ≤ horizon_of ac_prefix) = true := by
      exact List.all_eq_true.mp hd
    exact of_decide_eq_true (hall s hs)
  · intro hp
    exact List.all_eq_true.mpr (fun s hs => decide_eq_true (hp s hs))

def large_horizon_P (ac_prefix : ArrivalCurvePrefix) :
    BoolReflect (large_horizon ac_prefix) (large_horizon_dec ac_prefix) := by
  cases hdec : large_horizon_dec ac_prefix with
  | true => exact BoolReflect.isTrue ((large_horizon_iff ac_prefix).mp hdec)
  | false => exact BoolReflect.isFalse (fun hp => by
      have ht := (large_horizon_iff ac_prefix).mpr hp
      rw [hdec] at ht
      cases ht)

def no_inf_arrivals (ac_prefix : ArrivalCurvePrefix) : Bool :=
  decide (value_at ac_prefix 0 = 0)

def specified_bursts (ac_prefix : ArrivalCurvePrefix) : Bool :=
  decide (1 ∈ time_steps_of ac_prefix)

def ltn_steps (a b : duration × Nat) : Bool :=
  decide (a.1 < b.1) && decide (a.2 < b.2)

def sorted_ltn_steps (ac_prefix : ArrivalCurvePrefix) : Bool :=
  sortedBool ltn_steps (steps_of ac_prefix)

def valid_arrival_curve_prefix (ac_prefix : ArrivalCurvePrefix) : Prop :=
  positive_horizon ac_prefix = true ∧
  large_horizon ac_prefix ∧
  no_inf_arrivals ac_prefix = true ∧
  specified_bursts ac_prefix = true ∧
  sorted_ltn_steps ac_prefix = true

def valid_arrival_curve_prefix_dec (ac_prefix : ArrivalCurvePrefix) : Bool :=
  positive_horizon ac_prefix && large_horizon_dec ac_prefix &&
  no_inf_arrivals ac_prefix && specified_bursts ac_prefix &&
  sorted_ltn_steps ac_prefix

def valid_arrival_curve_prefix_P (ac_prefix : ArrivalCurvePrefix) :
    BoolReflect (valid_arrival_curve_prefix ac_prefix)
      (valid_arrival_curve_prefix_dec ac_prefix) := by
  have hlarge := large_horizon_iff ac_prefix
  have hiff : valid_arrival_curve_prefix_dec ac_prefix = true ↔
      valid_arrival_curve_prefix ac_prefix := by
    simp only [valid_arrival_curve_prefix_dec, valid_arrival_curve_prefix,
      Bool.and_eq_true, hlarge, and_assoc]
  cases hdec : valid_arrival_curve_prefix_dec ac_prefix with
  | true =>
      exact BoolReflect.isTrue (hiff.mp hdec)
  | false =>
      exact BoolReflect.isFalse (fun hp => by
        have ht := hiff.mpr hp
        rw [hdec] at ht
        cases ht)

def leq_steps (a b : duration × Nat) : Bool :=
  decide (a.1 ≤ b.1) && decide (a.2 ≤ b.2)

def sorted_leq_steps (ac_prefix : ArrivalCurvePrefix) : Bool :=
  sortedBool leq_steps (steps_of ac_prefix)

end Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
