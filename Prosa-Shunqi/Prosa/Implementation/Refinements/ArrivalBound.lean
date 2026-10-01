-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/arrival_bound.v

import Prosa.Implementation.Refinements.Refinements
import Prosa.Implementation.Definitions.ArrivalBound

/-! # Refinement of arrival bounds

A generic version of the arrival-bound definitions (over a type `T` with the CoqEAL operation classes) and the
refinements relating it, at the binary numbers `N`, to the natural-number definitions.

Representation (as in `Refinements`): Rocq cumulativity `Prop ≤ Type` is `PLift`; the source's `Type`-valued
`Global Instance`s are Lean definitions; MathComp's `last` in `step_at` is `List.getLastD`, as in the accepted
`step_at`; `sorted` is the accepted `sortedBool`; `has p s` is `s.any p`; `all p s` is `s.all p`; `transitive R`
is MathComp's `∀ y x z, R x y → R y z → R x z`; the MathComp equality on `N` (an `eqType` through `N_eqb`), on
lists and on pairs is `decide (_ = _)` over the derived decidable equalities, as for the accepted `eqType`s. -/

set_option linter.dupNamespace false
set_option warn.classDefReducibility false

namespace Prosa.Implementation.Refinements.ArrivalBound

open Prosa.Implementation.Refinements.Refinements
open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
open Prosa.Implementation.Definitions.ArrivalBound

-- The MathComp `eqType` structure of the binary numbers.
deriving instance DecidableEq for positive
deriving instance DecidableEq for N

/-! ### Generic definitions -/

/-- A generic task arrival bound: periodic, sporadic, or an arrival-curve prefix. -/
inductive task_arrivals_bound_T (T : Type) : Type where
  | Periodic_T : T → task_arrivals_bound_T T
  | Sporadic_T : T → task_arrivals_bound_T T
  | ArrivalPrefix_T : T × List (T × T) → task_arrivals_bound_T T

open task_arrivals_bound_T

/-- Equality of generic arrival bounds, attribute by attribute. -/
def taskab_eqdef_T {T : Type} [eq_of T] [eq_of (T × List (T × T))]
    (tb1 tb2 : task_arrivals_bound_T T) : Bool :=
  match tb1, tb2 with
  | Periodic_T p1, Periodic_T p2 => eq_op p1 p2
  | Sporadic_T s1, Sporadic_T s2 => eq_op s1 s2
  | ArrivalPrefix_T s1, ArrivalPrefix_T s2 => eq_op s1 s2
  | _, _ => false

/-- The horizon of a generic arrival-curve prefix. -/
def horizon_of_T {T : Type} (ac_prefix_vec : T × List (T × T)) : T := ac_prefix_vec.1

/-- The steps of a generic arrival-curve prefix. -/
def steps_of_T {T : Type} (ac_prefix_vec : T × List (T × T)) : List (T × T) := ac_prefix_vec.2

/-- The time steps of a generic arrival-curve prefix. -/
def time_steps_of_T {T : Type} (ac_prefix_vec : T × List (T × T)) : List T :=
  (steps_of_T ac_prefix_vec).map Prod.fst

/-- The last step `(duration, value)` with `duration ≤ t`. -/
def step_at_T {T : Type} [zero_of T] [leq_of T] (ac_prefix_vec : T × List (T × T)) (t : T) : T × T :=
  ((steps_of_T ac_prefix_vec).filter (fun step => leq_op step.1 t)).getLastD (zero_op, zero_op)

/-- The value of the last step with `duration ≤ t`. -/
def value_at_T {T : Type} [zero_of T] [leq_of T] (ac_prefix_vec : T × List (T × T)) (t : T) : T :=
  (step_at_T ac_prefix_vec t).2

/-- The generic periodic extension of an arrival-curve prefix. -/
def extrapolated_arrival_curve_T {T : Type} [zero_of T] [add_of T] [mul_of T] [div_of T] [mod_of T]
    [leq_of T] (ac_prefix_vec : T × List (T × T)) (t : T) : T :=
  let h := horizon_of_T ac_prefix_vec
  add_op (mul_op (div_op t h) (value_at_T ac_prefix_vec h)) (value_at_T ac_prefix_vec (mod_op t h))

/-- Steps strictly increasing in both components. -/
def ltn_steps_T {T : Type} [lt_of T] (a b : T × T) : Bool := lt_op a.1 b.1 && lt_op a.2 b.2

/-- Sortedness of the steps by `ltn_steps_T`. -/
def sorted_ltn_steps_T {T : Type} [lt_of T] (ac_prefix : T × List (T × T)) : Bool :=
  sortedBool ltn_steps_T (steps_of_T ac_prefix)

/-- Steps non-decreasing in both components. -/
def leq_steps_T {T : Type} [leq_of T] (a b : T × T) : Bool := leq_op a.1 b.1 && leq_op a.2 b.2

/-- A positive horizon. -/
def positive_horizon_T {T : Type} [zero_of T] [lt_of T] (ac_prefix : T × List (T × T)) : Bool :=
  lt_op zero_op (horizon_of_T ac_prefix)

/-- The horizon bounds the time steps. -/
def large_horizon_T {T : Type} [leq_of T] (ac_prefix : T × List (T × T)) : Bool :=
  (time_steps_of_T ac_prefix).all (fun s => leq_op s (horizon_of_T ac_prefix))

/-- No infinite arrivals: `value_at 0 = 0`. -/
def no_inf_arrivals_T {T : Type} [zero_of T] [eq_of T] [leq_of T] (ac_prefix : T × List (T × T)) : Bool :=
  eq_op (value_at_T ac_prefix zero_op) zero_op

/-- Bursts are specified: a time step equals `1`. -/
def specified_bursts_T {T : Type} [one_of T] [eq_of T] (ac_prefix : T × List (T × T)) : Bool :=
  (time_steps_of_T ac_prefix).any (fun step => eq_op step one_op)

/-- A valid generic arrival-curve prefix. -/
def valid_extrapolated_arrival_curve_T {T : Type} [zero_of T] [one_of T] [eq_of T] [leq_of T] [lt_of T]
    (ac_prefix : T × List (T × T)) : Bool :=
  positive_horizon_T ac_prefix && large_horizon_T ac_prefix && no_inf_arrivals_T ac_prefix &&
    specified_bursts_T ac_prefix && sorted_ltn_steps_T ac_prefix

/-! ### Conversions -/

/-- A binary arrival-curve prefix as a natural-number one. -/
def ACPrefixT_to_ACPrefix (ac_prefix_vec_T : N × List (N × N)) : ArrivalCurvePrefix :=
  (nat_of_bin (horizon_of_T ac_prefix_vec_T), m_tb2tn (steps_of_T ac_prefix_vec_T))

/-- Its graph relation. -/
def RArrivalCurvePrefix : ArrivalCurvePrefix → N × List (N × N) → Type := fun_hrel ACPrefixT_to_ACPrefix

/-- A natural-number arrival-curve prefix as a binary one. -/
def ACPrefix_to_ACPrefixT (ac_prefix_vec : ArrivalCurvePrefix) : N × List (N × N) :=
  (bin_of_nat (horizon_of ac_prefix_vec), m_tn2tb (steps_of ac_prefix_vec))

/-- A binary arrival bound as a natural-number one. -/
def task_abT_to_task_ab (ab : task_arrivals_bound_T N) : task_arrivals_bound :=
  match ab with
  | Periodic_T p => .Periodic (nat_of_bin p)
  | Sporadic_T m => .Sporadic (nat_of_bin m)
  | ArrivalPrefix_T ac_prefix_vec => .ArrivalPrefix (ACPrefixT_to_ACPrefix ac_prefix_vec)

/-- Its graph relation. -/
def Rtask_ab : task_arrivals_bound → task_arrivals_bound_T N → Type := fun_hrel task_abT_to_task_ab

/-- A natural-number arrival bound as a binary one. -/
def task_ab_to_task_abT (ab : task_arrivals_bound) : task_arrivals_bound_T N :=
  match ab with
  | .Periodic p => Periodic_T (bin_of_nat p)
  | .Sporadic m => Sporadic_T (bin_of_nat m)
  | .ArrivalPrefix ac_prefix_vec => ArrivalPrefix_T (ACPrefix_to_ACPrefixT ac_prefix_vec)

/-! ### Transitivity of the step orders -/

/-- `leq_steps_T` is transitive. -/
theorem leq_stepsT_is_transitive :
    ∀ y x z : N × N, leq_steps_T x y = true → leq_steps_T y z = true → leq_steps_T x z = true := by
  intro y x z hxy hyz
  simp only [leq_steps_T, Bool.and_eq_true, leq_op_N, decide_eq_true_eq] at *
  omega

/-- `ltn_steps_T` is transitive. -/
theorem ltn_stepsT_is_transitive :
    ∀ y x z : N × N, ltn_steps_T x y = true → ltn_steps_T y z = true → ltn_steps_T x z = true := by
  intro y x z hxy hyz
  simp only [ltn_steps_T, Bool.and_eq_true, lt_op_N, decide_eq_true_eq] at *
  omega

/-! ### Refinements -/

theorem prod_R_Rnat_eq {a : Nat × Nat} {a' : N × N} (h : prod_R Rnat Rnat a a') :
    nat_of_bin a'.1 = a.1 ∧ nat_of_bin a'.2 = a.2 := by
  cases h with
  | pair_R h1 h2 => exact ⟨Rnat_eq h1, Rnat_eq h2⟩

theorem list_R_steps_eq {xs : List (Nat × Nat)} {xs' : List (N × N)}
    (h : list_R (prod_R Rnat Rnat) xs xs') : m_tb2tn xs' = xs := by
  induction h with
  | nil_R => rfl
  | cons_R hx _ ih =>
    obtain ⟨h1, h2⟩ := prod_R_Rnat_eq hx
    simp only [m_tb2tn, List.map_cons, tb2tn, tmap] at ih ⊢
    rw [ih, h1, h2]

/-- Refinement of `leq_steps`. -/
def refine_leq_steps :
    refines (hrespectful (prod_R Rnat Rnat) (hrespectful (prod_R Rnat Rnat) bool_R)) leq_steps leq_steps_T :=
  ⟨fun _ _ Ra _ _ Rb => bool_R_of_eq (by
    obtain ⟨a1, a2⟩ := prod_R_Rnat_eq Ra
    obtain ⟨b1, b2⟩ := prod_R_Rnat_eq Rb
    simp only [leq_steps, leq_steps_T, leq_op_N, a1, a2, b1, b2])⟩

/-- Refinement of `ltn_steps`. -/
def refine_ltn_steps :
    refines (hrespectful (prod_R Rnat Rnat) (hrespectful (prod_R Rnat Rnat) bool_R)) ltn_steps ltn_steps_T :=
  ⟨fun _ _ Ra _ _ Rb => bool_R_of_eq (by
    obtain ⟨a1, a2⟩ := prod_R_Rnat_eq Ra
    obtain ⟨b1, b2⟩ := prod_R_Rnat_eq Rb
    simp only [ltn_steps, ltn_steps_T, lt_op_N, a1, a2, b1, b2])⟩

private theorem sortedBoolFrom_related {R : Nat × Nat → Nat × Nat → Bool} {R' : N × N → N × N → Bool}
    (hR : ∀ a a' b b', prod_R Rnat Rnat a a' → prod_R Rnat Rnat b b' → R a b = R' a' b') :
    ∀ {xs : List (Nat × Nat)} {xs' : List (N × N)}, list_R (prod_R Rnat Rnat) xs xs' →
      ∀ (x : Nat × Nat) (x' : N × N), prod_R Rnat Rnat x x' →
        sortedBoolFrom R x xs = sortedBoolFrom R' x' xs'
  | _, _, .nil_R, _, _, _ => rfl
  | _, _, .cons_R hy hs, x, x', hx => by
      simp only [sortedBoolFrom, hR _ _ _ _ hx hy, sortedBoolFrom_related hR hs _ _ hy]

private theorem sortedBool_related {R : Nat × Nat → Nat × Nat → Bool} {R' : N × N → N × N → Bool}
    (hR : ∀ a a' b b', prod_R Rnat Rnat a a' → prod_R Rnat Rnat b b' → R a b = R' a' b')
    {xs : List (Nat × Nat)} {xs' : List (N × N)} (h : list_R (prod_R Rnat Rnat) xs xs') :
    sortedBool R xs = sortedBool R' xs' := by
  cases h with
  | nil_R => rfl
  | cons_R hx hs => exact sortedBoolFrom_related hR hs _ _ hx

/-- Refinement of the `ltn_steps` sortedness. -/
def refine_ltn_steps_sorted :
    ∀ (xs : List (Nat × Nat)) (xs' : List (N × N)), refines (list_R (prod_R Rnat Rnat)) xs xs' →
      refines bool_R (sortedBool ltn_steps xs) (sortedBool ltn_steps_T xs') :=
  fun _ _ Rxs => ⟨bool_R_of_eq (sortedBool_related
    (fun _ _ _ _ ha hb => bool_R_eq (refine_ltn_steps.refines_rel _ _ ha _ _ hb)) Rxs.refines_rel)⟩

/-- Refinement of the `leq_steps` sortedness. -/
def refine_leq_steps_sorted :
    ∀ (xs : List (Nat × Nat)) (xs' : List (N × N)), refines (list_R (prod_R Rnat Rnat)) xs xs' →
      refines bool_R (sortedBool leq_steps xs) (sortedBool leq_steps_T xs') :=
  fun _ _ Rxs => ⟨bool_R_of_eq (sortedBool_related
    (fun _ _ _ _ ha hb => bool_R_eq (refine_leq_steps.refines_rel _ _ ha _ _ hb)) Rxs.refines_rel)⟩

theorem prefix_R_eq {e : ArrivalCurvePrefix} {e' : N × List (N × N)}
    (h : prod_R Rnat (list_R (prod_R Rnat Rnat)) e e') : ACPrefixT_to_ACPrefix e' = e := by
  cases h with
  | pair_R h1 h2 =>
    simp only [ACPrefixT_to_ACPrefix, horizon_of_T, steps_of_T, Rnat_eq h1, list_R_steps_eq h2]

private theorem step_at_T_eq (e' : N × List (N × N)) (t' : N) :
    tb2tn (step_at_T e' t') = step_at (ACPrefixT_to_ACPrefix e') (nat_of_bin t') := by
  obtain ⟨h, st⟩ := e'
  simp only [step_at_T, step_at, steps_of_T, steps_of, ACPrefixT_to_ACPrefix, m_tb2tn]
  induction st using List.reverseRecOn with
  | nil => rfl
  | append_singleton st x ih =>
    simp only [List.filter_append, List.map_append, List.filter_cons, List.filter_nil, List.map_cons,
      List.map_nil]
    have hx : (decide ((tb2tn x).1 ≤ nat_of_bin t')) = leq_op x.1 t' := by
      rw [leq_op_N]; rfl
    rw [hx]
    cases leq_op x.1 t'
    · simp only [Bool.false_eq_true, if_false, List.append_nil]; exact ih
    · simp only [if_true, List.getLastD_eq_getLast?, List.getLast?_append, List.getLast?_singleton,
        Option.some_or, Option.getD_some]

/-- Refinement of `value_at`. -/
def refine_value_at :
    refines (hrespectful (prod_R Rnat (list_R (prod_R Rnat Rnat))) (hrespectful Rnat Rnat)) value_at value_at_T :=
  ⟨fun _ e' Re _ t' Rt => Rnat_intro (by
    have := congrArg Prod.snd (step_at_T_eq e' t')
    simp only [tb2tn, tmap] at this
    simp only [value_at_T, value_at, this, prefix_R_eq Re, Rnat_eq Rt])⟩

/-- Refinement of `time_steps_of`. -/
def refine_get_time_steps :
    refines (hrespectful (prod_R Rnat (list_R (prod_R Rnat Rnat))) (list_R Rnat)) time_steps_of time_steps_of_T :=
  ⟨fun _ _ Re => by
    cases Re with
    | pair_R _ h2 =>
      exact list_R_map (fun _ _ hx => by cases hx with | pair_R h1 _ => exact h1) h2⟩

private theorem nat_of_bin_mul_op (a b : N) : nat_of_bin (mul_op a b) = nat_of_bin a * nat_of_bin b :=
  nat_of_bin_mul a b

/-- Refinement of `extrapolated_arrival_curve`. -/
def refine_arrival_curve_prefix :
    refines (hrespectful (prod_R Rnat (list_R (prod_R Rnat Rnat))) (hrespectful Rnat Rnat))
      extrapolated_arrival_curve extrapolated_arrival_curve_T :=
  ⟨fun e e' Re t t' Rt => Rnat_intro (by
    have hv : ∀ u : N, nat_of_bin (value_at_T e' u) = value_at e (nat_of_bin u) := fun u =>
      Rnat_eq (refine_value_at.refines_rel e e' Re (nat_of_bin u) u (Rnat_intro rfl))
    have hh : nat_of_bin (horizon_of_T e') = horizon_of e := by
      rw [← prefix_R_eq Re]; rfl
    simp only [extrapolated_arrival_curve_T, extrapolated_arrival_curve, nat_of_bin_add_op, nat_of_bin_mul_op,
      nat_of_bin_div_op, nat_of_bin_mod_op, hv, hh, Rnat_eq Rt])⟩

/-- Refinement of the `ArrivalPrefix` constructor. -/
def refine_ArrivalPrefix :
    refines (hrespectful (prod_R Rnat (list_R (prod_R Rnat Rnat))) Rtask_ab) task_arrivals_bound.ArrivalPrefix
      ArrivalPrefix_T :=
  ⟨fun _ _ Re => ⟨by simp only [task_abT_to_task_ab, prefix_R_eq Re]⟩⟩

/-- The MathComp equality on lists of binary numbers. -/
instance eq_listN : eq_of (List N) := ⟨fun x y => decide (x = y)⟩

/-- The MathComp equality on binary arrival-curve prefixes. -/
instance eq_NlistNN : eq_of (N × List (N × N)) := ⟨fun x y => decide (x = y)⟩

/-- The generic equality on binary arrival bounds. -/
instance eq_taskab : eq_of (task_arrivals_bound_T N) := ⟨taskab_eqdef_T⟩

private theorem m_tb2tn_inj {xs ys : List (N × N)} (h : m_tb2tn xs = m_tb2tn ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => simp [m_tb2tn] at h
  | cons x xs ih =>
    cases ys with
    | nil => simp [m_tb2tn] at h
    | cons y ys =>
      simp only [m_tb2tn, List.map_cons, List.cons.injEq, tb2tn, tmap, Prod.mk.injEq] at h
      obtain ⟨⟨h1, h2⟩, h3⟩ := h
      have hx : x = y := Prod.ext (nat_of_bin_inj _ _ h1) (nat_of_bin_inj _ _ h2)
      rw [hx, ih h3]

private theorem ACPrefixT_to_ACPrefix_inj {a b : N × List (N × N)}
    (h : ACPrefixT_to_ACPrefix a = ACPrefixT_to_ACPrefix b) : a = b := by
  obtain ⟨ha, sa⟩ := a
  obtain ⟨hb, sb⟩ := b
  simp only [ACPrefixT_to_ACPrefix, horizon_of_T, steps_of_T, Prod.mk.injEq] at h
  rw [nat_of_bin_inj _ _ h.1, m_tb2tn_inj h.2]

private theorem task_ab_eq_spec (x' y' : task_arrivals_bound_T N) :
    decide (task_abT_to_task_ab x' = task_abT_to_task_ab y') = taskab_eqdef_T x' y' := by
  cases x' with
  | Periodic_T a =>
    cases y' with
    | Periodic_T b =>
      simp only [task_abT_to_task_ab, taskab_eqdef_T, eq_op_N, task_arrivals_bound.Periodic.injEq]
    | Sporadic_T b => simp [task_abT_to_task_ab, taskab_eqdef_T]
    | ArrivalPrefix_T b => simp [task_abT_to_task_ab, taskab_eqdef_T]
  | Sporadic_T a =>
    cases y' with
    | Periodic_T b => simp [task_abT_to_task_ab, taskab_eqdef_T]
    | Sporadic_T b =>
      simp only [task_abT_to_task_ab, taskab_eqdef_T, eq_op_N, task_arrivals_bound.Sporadic.injEq]
    | ArrivalPrefix_T b => simp [task_abT_to_task_ab, taskab_eqdef_T]
  | ArrivalPrefix_T a =>
    cases y' with
    | Periodic_T b => simp [task_abT_to_task_ab, taskab_eqdef_T]
    | Sporadic_T b => simp [task_abT_to_task_ab, taskab_eqdef_T]
    | ArrivalPrefix_T b =>
      simp only [task_abT_to_task_ab, taskab_eqdef_T, task_arrivals_bound.ArrivalPrefix.injEq]
      show decide _ = decide _
      exact decide_eq_decide.mpr ⟨ACPrefixT_to_ACPrefix_inj, fun h => h ▸ rfl⟩

/-- Refinement of the equality on arrival bounds. -/
def refine_task_ab_eq :
    refines (hrespectful Rtask_ab (hrespectful Rtask_ab bool_R))
      (fun x y : task_arrivals_bound => decide (x = y)) (eq_op : task_arrivals_bound_T N → _ → Bool) :=
  ⟨fun x x' Rx y y' Ry => bool_R_of_eq (by
    rw [← Rx.down, ← Ry.down]
    exact task_ab_eq_spec x' y')⟩

end Prosa.Implementation.Refinements.ArrivalBound
