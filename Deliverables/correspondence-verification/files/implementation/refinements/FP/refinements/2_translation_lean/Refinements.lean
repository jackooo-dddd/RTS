-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/FP/refinements.v

import Prosa.Implementation.Refinements.FP.FastSearchSpace

/-! # Refinements of the fixed-priority RTA definitions

Generic versions of the fixed-priority definitions (over a type `T` with the CoqEAL operation classes) and the
refinements relating them, at the binary numbers `N`, to the natural-number versions.

Representation (as in `Refinements`, `ArrivalBound` and `Task`): Rocq cumulativity `Prop ≤ Type` is `PLift`; the
source's `Type`-valued `Global Instance`s are Lean definitions and its `Local Instance` (`refine_search_space_emax_h`)
is not a public declaration; the file-wide `#[local] Existing Instance NumericFPAscending` is the accepted
`NumericFPAscending Task`, passed explicitly; the section's operation classes are instance binders and its
`Context {eq_of2 : eq_of task_T}` is a named instance binder, each definition taking only those it uses, in the order
of the elaborated types; `foldr +%C 0%C` is `List.foldr add_op zero_op`; `iota_T a Δ` with `Δ : N` coerced to `nat`
is `iota_T a (nat_of_bin Δ)`; `0` at `N` is `N.N0`; MathComp equality tests are `decide (x = y)`; the instances are
those resolved in the source (the latest declared, i.e. this file's `eq_NlistNN`/`eq_taskab`). -/

set_option linter.dupNamespace false
set_option warn.classDefReducibility false

namespace Prosa.Implementation.Refinements.FP.Refinements

open Prosa.Behavior.Time
open Prosa.Util.Sum
open Prosa.Model.Task.Concept
open Prosa.Model.Priority.Definitions
open Prosa.Model.Priority.NumericFixedPriority
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
open Prosa.Implementation.Definitions.ArrivalBound
open Prosa.Implementation.Definitions.Task
open Prosa.Implementation.Refinements.Refinements
open Prosa.Implementation.Refinements.ArrivalBound
open Prosa.Implementation.Refinements.Task
open Prosa.Implementation.Refinements.ArrivalCurve
open Prosa.Implementation.Refinements.FP.FastSearchSpace

/-! ### Generic definitions -/

/-- Higher-or-equal priority on generic tasks. -/
def hep_task_T {T : Type} [leq_of T] (tsk_o tsk : task_T T) : Bool :=
  leq_op (task_T.task_priority_T tsk) (task_T.task_priority_T tsk_o)

/-- Generic total request-bound function of the higher-or-equal-priority tasks. -/
def total_hep_rbf_T {T : Type} [zero_of T] [one_of T] [add_of T] [mul_of T] [div_of T] [mod_of T] [leq_of T]
    (ts : List (task_T T)) (tsk : task_T T) (Δ : T) : T :=
  let hep_ts := ts.filter (fun tsk' => hep_task_T tsk' tsk)
  let work_ts := hep_ts.map (fun tsk' => task_rbf_T tsk' Δ)
  work_ts.foldr add_op zero_op

/-- Higher-or-equal priority and a different generic task. -/
def ohep_task_T {T : Type} [leq_of T] [eq_of2 : eq_of (task_T T)] (tsk_o tsk : task_T T) : Bool :=
  hep_task_T tsk_o tsk && !(eq_of2.eq_op tsk_o tsk)

/-- Generic total request-bound function of the other higher-or-equal-priority tasks. -/
def total_ohep_rbf_T {T : Type} [zero_of T] [one_of T] [add_of T] [mul_of T] [div_of T] [mod_of T] [leq_of T]
    [eq_of2 : eq_of (task_T T)] (ts : List (task_T T)) (tsk : task_T T) (Δ : T) : T :=
  let hep_ts := ts.filter (fun tsk' => ohep_task_T tsk' tsk)
  let work_ts := hep_ts.map (fun tsk' => task_rbf_T tsk' Δ)
  work_ts.foldr add_op zero_op

/-- Generic check of a point under the fully-preemptive policy. -/
def check_point_FP_T {T : Type} [zero_of T] [one_of T] [add_of T] [mul_of T] [div_of T] [mod_of T] [leq_of T]
    [eq_of2 : eq_of (task_T T)] (ts : List (task_T T)) (tsk : task_T T) (R : T) (P : T × T) : Bool :=
  leq_op (add_op (task_rbf_T tsk (add_op P.1 one_op)) (total_ohep_rbf_T ts tsk (add_op P.1 P.2))) (add_op P.1 P.2) &&
    leq_op P.2 R

/-- Generic blocking bound under nonpreemptive policies. -/
def blocking_bound_NP_T {T : Type} [zero_of T] [one_of T] [sub_of T] [leq_of T] [lt_of T]
    (ts : List (task_T T)) (tsk : task_T T) : T :=
  let lp_ts := ts.filter (fun tsk_o => !hep_task_T tsk_o tsk)
  let block_ts := lp_ts.map (fun tsk_o => sub_op (task_T.task_cost_T tsk_o) one_op)
  block_ts.foldr maxn_T zero_op

/-- Generic check of a point under the fully-nonpreemptive policy. -/
def check_point_NP_T {T : Type} [zero_of T] [one_of T] [sub_of T] [add_of T] [mul_of T] [div_of T] [mod_of T]
    [leq_of T] [lt_of T] [eq_of2 : eq_of (task_T T)] (ts : List (task_T T)) (tsk : task_T T) (R : T) (P : T × T) :
    Bool :=
  leq_op (add_op (add_op (blocking_bound_NP_T ts tsk)
      (sub_op (task_rbf_T tsk (add_op P.1 one_op)) (sub_op (task_T.task_cost_T tsk) one_op)))
      (total_ohep_rbf_T ts tsk (add_op P.1 P.2))) (add_op P.1 P.2) &&
    leq_op (add_op P.2 (sub_op (task_T.task_cost_T tsk) one_op)) R

/-! ### Definitions at the binary numbers -/

/-- `iota` at `N`. -/
def iota_N (a Δ : N) : List N := iota_T a (nat_of_bin Δ)

/-- The binary search space in `[l * h, r * h)`. -/
def search_space_emax_FP_h_N (tsk : task_T N) (l r : N) : List N :=
  let h := get_horizon_of_task_T tsk
  let offsets := (iota_N l r).map (fun i => N.mul h i)
  let emax_offsets := repeat_steps_with_offset_T tsk offsets
  emax_offsets.map predn_T

/-- The binary search space. -/
def search_space_emax_FP_N (tsk : task_T N) (L : N) : List N :=
  let h := get_horizon_of_task_T tsk
  search_space_emax_FP_h_N tsk N.N0 (add_op (div_op L h) one_op)

/-! ### Equality instances -/

/-- MathComp equality on lists of binary numbers. -/
instance eq_listN : eq_of (List N) := ⟨fun x y => decide (x = y)⟩

/-- MathComp equality on lists of pairs of binary numbers. -/
instance eq_listNN : eq_of (List (N × N)) := ⟨fun x y => decide (x = y)⟩

/-- MathComp equality on binary arrival-curve prefixes. -/
instance eq_NlistNN : eq_of (N × List (N × N)) := ⟨fun x y => decide (x = y)⟩

/-- Generic equality on binary arrival bounds. -/
instance eq_taskab : eq_of (task_arrivals_bound_T N) := ⟨@taskab_eqdef_T N _ eq_NlistNN⟩

/-- Generic equality on binary tasks. -/
instance eq_task : eq_of (task_T N) := ⟨@task_eqdef_T N _ eq_taskab⟩

/-! ### Local helpers (not source declarations) -/

private theorem task_rbf_N (tsk : task_T N) (d : N) :
    task_rbf (taskT_to_task tsk) (nat_of_bin d) = nat_of_bin (task_rbf_T tsk d) :=
  (Rnat_eq ((refine_task_rbf.refines_rel _ tsk ⟨rfl⟩ _ d (Rnat_intro rfl)))).symm

private theorem hep_N (t1 t2 : task_T N) :
    (NumericFPAscending Task).hep_task (taskT_to_task t1) (taskT_to_task t2) = hep_task_T t1 t2 := by
  obtain ⟨_, _, _, _, p1⟩ := t1
  obtain ⟨_, _, _, _, p2⟩ := t2
  simp only [hep_task_T, leq_op_N]
  rfl

private def list_R_Rtask_map : ∀ ts : List (task_T N), list_R Rtask (ts.map taskT_to_task) ts
  | [] => .nil_R
  | _ :: ts => .cons_R ⟨rfl⟩ (list_R_Rtask_map ts)

private theorem list_R_Rtask_eq {ts : List Task} {ts' : List (task_T N)} (h : list_R Rtask ts ts') :
    ts = ts'.map taskT_to_task := by
  induction h with
  | nil_R => rfl
  | cons_R hx _ ih => rw [← hx.down, ih]; rfl

private theorem task_eqdef_N (t1 t2 : task_T N) :
    task_eqdef (taskT_to_task t1) (taskT_to_task t2) = (eq_task.eq_op t1 t2 : Bool) := by
  have hab : ∀ a b : task_arrivals_bound_T N,
      decide (task_abT_to_task_ab a = task_abT_to_task_ab b) = (eq_taskab.eq_op a b : Bool) := fun a b =>
    bool_R_eq (refine_task_ab_eq.refines_rel _ a ⟨rfl⟩ _ b ⟨rfl⟩)
  have hn : ∀ a b : N, decide (nat_of_bin a = nat_of_bin b) = N.eqb a b := by
    intro a b
    rw [← eq_op_N]
    rfl
  obtain ⟨i1, c1, a1, d1, p1⟩ := t1
  obtain ⟨i2, c2, a2, d2, p2⟩ := t2
  have e : (eq_task.eq_op ⟨i1, c1, a1, d1, p1⟩ ⟨i2, c2, a2, d2, p2⟩ : Bool) =
      (N.eqb i1 i2 && N.eqb c1 c2 && eq_taskab.eq_op a1 a2 && N.eqb d1 d2 && N.eqb p1 p2) := rfl
  rw [e]
  show (decide (nat_of_bin i1 = nat_of_bin i2) && decide (nat_of_bin c1 = nat_of_bin c2) &&
      decide (task_abT_to_task_ab a1 = task_abT_to_task_ab a2) && decide (nat_of_bin d1 = nat_of_bin d2) &&
      decide (nat_of_bin p1 = nat_of_bin p2)) = _
  exact congrArg₂ (· && ·) (congrArg₂ (· && ·) (congrArg₂ (· && ·) (congrArg₂ (· && ·) (hn _ _) (hn _ _))
    (hab _ _)) (hn _ _)) (hn _ _)

private theorem task_eq_iff (t1 t2 : task_T N) :
    decide (taskT_to_task t1 ≠ taskT_to_task t2) = !(eq_task.eq_op t1 t2 : Bool) := by
  rw [← task_eqdef_N]
  have := (eqn_task (taskT_to_task t1) (taskT_to_task t2))
  cases h : task_eqdef (taskT_to_task t1) (taskT_to_task t2) with
  | true =>
      rw [h] at this; cases this with
      | isTrue e => simp [e]
  | false =>
      rw [h] at this; cases this with
      | isFalse e => simp [e]

private theorem ohep_N (t1 t2 : task_T N) :
    ohep_task (taskT_to_task t1) (taskT_to_task t2) = ohep_task_T t1 t2 := by
  simp only [ohep_task, ohep_task_T, hep_N, task_eq_iff]

/-! ### Refinements -/

/-- Refinement of the fixed-priority search space. -/
def refine_search_space_emax :
    ∀ tsk : task_T N,
      refines (hrespectful Rnat (list_R Rnat)) (search_space_emax_FP (taskT_to_task tsk)) (search_space_emax_FP_N tsk) :=
  fun tsk => ⟨fun δ δ' Rδ => by
    have hh : get_horizon_of_task (taskT_to_task tsk) = nat_of_bin (get_horizon_of_task_T tsk) :=
      (Rnat_eq (refine_get_horizon_of_task.refines_rel _ tsk ⟨rfl⟩)).symm
    have hbound : δ / get_horizon_of_task (taskT_to_task tsk) + 1 =
        nat_of_bin (add_op (div_op δ' (get_horizon_of_task_T tsk)) one_op) := by
      rw [nat_of_bin_add_op, nat_of_bin_div_op, nat_of_bin_one, Rnat_eq Rδ, hh]
    simp only [search_space_emax_FP, search_space_emax_FP_h, search_space_emax_FP_N, search_space_emax_FP_h_N, iota_N]
    rw [hbound]
    refine list_R_map (fun x x' Rx => Rnat_pred.refines_rel x x' Rx) ?_
    refine refine_repeat_steps_with_offset.refines_rel _ tsk ⟨rfl⟩ _ _ ?_
    refine list_R_map (rA := Rnat) (fun x x' Rx => Rnat_intro ?_) ?_
    · show nat_of_bin (N.mul (get_horizon_of_task_T tsk) x') = get_horizon_of_task (taskT_to_task tsk) * x
      rw [nat_of_bin_mul, hh, Rnat_eq Rx]
    · rw [show (0 : Nat) = nat_of_bin N.N0 from rfl]
      exact refine_iota.go _ _ _ (Rnat_intro rfl)⟩

/-- Refinement of the higher-or-equal-priority test. -/
def refine_hep_task :
    refines (hrespectful Rtask (hrespectful Rtask bool_R)) (NumericFPAscending Task).hep_task hep_task_T :=
  ⟨fun _ t1' R1 _ t2' R2 => bool_R_of_eq (by rw [← R1.down, ← R2.down, hep_N])⟩

/-- Refinement of the total request-bound function of the higher-or-equal-priority tasks. -/
def refine_total_hep_rbf :
    refines (hrespectful (list_R Rtask) (hrespectful Rtask (hrespectful Rnat Rnat))) total_hep_rbf total_hep_rbf_T :=
  ⟨fun ts ts' Rts tsk tsk' Rtsk Δ Δ' RΔ =>
    (refine_foldr ts ts' (fun o => (NumericFPAscending Task).hep_task o tsk) (fun o => hep_task_T o tsk')
      (fun o => task_request_bound_function o Δ) (fun o => task_rbf_T o Δ') Rtask ⟨Rts⟩
      ⟨fun o o' Ro => refine_task_rbf.refines_rel o o' Ro Δ Δ' RΔ⟩
      ⟨fun o o' Ro => refine_hep_task.refines_rel o o' Ro tsk tsk' Rtsk⟩).refines_rel⟩

/-- Refinement of the total request-bound function of the higher-or-equal-priority tasks, at converted tasks. -/
def refine_total_hep_rbf' :
    ∀ (ts : List (task_T N)) (tsk : task_T N),
      refines (hrespectful Rnat Rnat) (total_hep_rbf (ts.map taskT_to_task) (taskT_to_task tsk)) (total_hep_rbf_T ts tsk) :=
  fun ts tsk => ⟨fun Δ Δ' RΔ => refine_total_hep_rbf.refines_rel _ ts (list_R_Rtask_map ts) _ tsk ⟨rfl⟩ Δ Δ' RΔ⟩

/-- Refinement of the task equality. -/
def refine_task_eqdef : refines (hrespectful Rtask (hrespectful Rtask bool_R)) task_eqdef (@task_eqdef_T N _ eq_taskab) :=
  ⟨fun _ t1' R1 _ t2' R2 => bool_R_of_eq (by rw [← R1.down, ← R2.down]; exact task_eqdef_N t1' t2')⟩

/-- Refinement of the other-higher-or-equal-priority test. -/
def refine_ohep_task : refines (hrespectful Rtask (hrespectful Rtask bool_R)) ohep_task ohep_task_T :=
  ⟨fun _ t1' R1 _ t2' R2 => bool_R_of_eq (by rw [← R1.down, ← R2.down, ohep_N])⟩

/-- Refinement of the total request-bound function of the other higher-or-equal-priority tasks. -/
def refine_total_ohep_rbf :
    refines (hrespectful (list_R Rtask) (hrespectful Rtask (hrespectful Rnat Rnat))) total_ohep_rbf total_ohep_rbf_T :=
  ⟨fun ts ts' Rts tsk tsk' Rtsk Δ Δ' RΔ =>
    (refine_foldr ts ts' (fun o => ohep_task o tsk) (fun o => ohep_task_T o tsk')
      (fun o => task_request_bound_function o Δ) (fun o => task_rbf_T o Δ') Rtask ⟨Rts⟩
      ⟨fun o o' Ro => refine_task_rbf.refines_rel o o' Ro Δ Δ' RΔ⟩
      ⟨fun o o' Ro => refine_ohep_task.refines_rel o o' Ro tsk tsk' Rtsk⟩).refines_rel⟩

private theorem total_ohep_N {ts : List Task} {ts' : List (task_T N)} (Rts : list_R Rtask ts ts') {tsk : Task}
    {tsk' : task_T N} (Rtsk : Rtask tsk tsk') {Δ : Nat} {Δ' : N} (RΔ : Rnat Δ Δ') :
    nat_of_bin (total_ohep_rbf_T ts' tsk' Δ') = total_ohep_rbf ts tsk Δ :=
  Rnat_eq (refine_total_ohep_rbf.refines_rel ts ts' Rts tsk tsk' Rtsk Δ Δ' RΔ)

/-- Refinement of the fully-preemptive check of a point. -/
def refine_check_point :
    refines (hrespectful (list_R Rtask) (hrespectful Rtask (hrespectful Rnat (hrespectful (prod_R Rnat Rnat) bool_R))))
      check_point_FP check_point_FP_T :=
  ⟨fun ts ts' Rts tsk tsk' Rtsk R R' RR P P' RP => bool_R_of_eq (by
    obtain ⟨a, f⟩ := P
    obtain ⟨a', f'⟩ := P'
    cases RP with
    | pair_R Ra Rf =>
      have h1 : nat_of_bin (task_rbf_T tsk' (add_op a' one_op)) = task_rbf tsk (a + 1) := by
        rw [← Rtsk.down, ← task_rbf_N, nat_of_bin_add_op, nat_of_bin_one, Rnat_eq Ra]
      have h2 := total_ohep_N Rts Rtsk (Δ := a + f) (Δ' := add_op a' f')
        (Rnat_intro (by rw [nat_of_bin_add_op, Rnat_eq Ra, Rnat_eq Rf]))
      simp only [check_point_FP, check_point_FP_T, leq_op_N, nat_of_bin_add_op, h1, h2, Rnat_eq Ra, Rnat_eq Rf,
        Rnat_eq RR])⟩

/-- Refinement of the fully-preemptive check of a point, at converted tasks. -/
def refine_check_point' :
    ∀ (ts : List (task_T N)) (tsk : task_T N),
      refines (hrespectful Rnat (hrespectful (prod_R Rnat Rnat) bool_R))
        (check_point_FP (ts.map taskT_to_task) (taskT_to_task tsk)) (check_point_FP_T ts tsk) :=
  fun ts tsk => ⟨fun R R' RR P P' RP => refine_check_point.refines_rel _ ts (list_R_Rtask_map ts) _ tsk ⟨rfl⟩ R R' RR P P' RP⟩

/-- Refinement of the blocking bound. -/
def refine_blocking_bound :
    refines (hrespectful (list_R Rtask) (hrespectful Rtask Rnat)) blocking_bound_NP blocking_bound_NP_T :=
  ⟨fun ts ts' Rts tsk tsk' Rtsk =>
    (refine_foldr_max ts ts' (fun o => !(NumericFPAscending Task).hep_task o tsk) (fun o => !hep_task_T o tsk')
      (fun o => task_cost o - 1) (fun o => sub_op (task_T.task_cost_T o) one_op) Rtask ⟨Rts⟩
      ⟨fun o o' Ro => Rnat_intro (by
        rw [← Ro.down, nat_of_bin_sub_op, nat_of_bin_one]
        obtain ⟨_, _, _, _, _⟩ := o'
        rfl)⟩
      ⟨fun o o' Ro => bool_R_of_eq (by rw [← Ro.down, ← Rtsk.down, hep_N])⟩).refines_rel⟩

/-- Refinement of the blocking bound, at converted tasks. -/
def refine_blocking_bound' :
    ∀ (ts : List (task_T N)) (tsk : task_T N),
      refines Rnat (blocking_bound_NP (ts.map taskT_to_task) (taskT_to_task tsk)) (blocking_bound_NP_T ts tsk) :=
  fun ts tsk => ⟨refine_blocking_bound.refines_rel _ ts (list_R_Rtask_map ts) _ tsk ⟨rfl⟩⟩

/-- Refinement of the fully-nonpreemptive check of a point. -/
def refine_check_point_NP :
    refines (hrespectful (list_R Rtask) (hrespectful Rtask (hrespectful Rnat (hrespectful (prod_R Rnat Rnat) bool_R))))
      check_point_NP check_point_NP_T :=
  ⟨fun ts ts' Rts tsk tsk' Rtsk R R' RR P P' RP => bool_R_of_eq (by
    obtain ⟨a, f⟩ := P
    obtain ⟨a', f'⟩ := P'
    cases RP with
    | pair_R Ra Rf =>
      have h1 : nat_of_bin (task_rbf_T tsk' (add_op a' one_op)) = task_rbf tsk (a + 1) := by
        rw [← Rtsk.down, ← task_rbf_N, nat_of_bin_add_op, nat_of_bin_one, Rnat_eq Ra]
      have h2 := total_ohep_N Rts Rtsk (Δ := a + f) (Δ' := add_op a' f')
        (Rnat_intro (by rw [nat_of_bin_add_op, Rnat_eq Ra, Rnat_eq Rf]))
      have h3 := Rnat_eq (refine_blocking_bound.refines_rel ts ts' Rts tsk tsk' Rtsk)
      have h4 : nat_of_bin (task_T.task_cost_T tsk') = task_cost tsk := by
        rw [← Rtsk.down]; obtain ⟨_, _, _, _, _⟩ := tsk'; rfl
      simp only [check_point_NP, check_point_NP_T, leq_op_N, nat_of_bin_add_op, nat_of_bin_sub_op, nat_of_bin_one,
        h1, h2, h3, h4, Rnat_eq Ra, Rnat_eq Rf, Rnat_eq RR])⟩

/-- Refinement of the fully-nonpreemptive check of a point, at converted tasks. -/
def refine_check_point_NP' :
    ∀ (ts : List (task_T N)) (tsk : task_T N),
      refines (hrespectful Rnat (hrespectful (prod_R Rnat Rnat) bool_R))
        (check_point_NP (ts.map taskT_to_task) (taskT_to_task tsk)) (check_point_NP_T ts tsk) :=
  fun ts tsk => ⟨fun R R' RR P P' RP =>
    refine_check_point_NP.refines_rel _ ts (list_R_Rtask_map ts) _ tsk ⟨rfl⟩ R R' RR P P' RP⟩

end Prosa.Implementation.Refinements.FP.Refinements
