-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: implementation/refinements/EDF/refinements.v

import Prosa.Implementation.Refinements.EDF.FastSearchSpace

/-! # Refinements of the earliest-deadline-first RTA definitions

Generic versions of the EDF definitions (over a type `T` with the CoqEAL operation classes) and the refinements
relating them, at the binary numbers `N`, to the natural-number versions.

Representation (as in `Refinements`, `ArrivalBound`, `Task` and `FP.Refinements`): Rocq cumulativity `Prop ≤ Type`
is `PLift`; the source's `Type`-valued `Global Instance`s are Lean definitions and its `Local Instance`s
(`refine_task_search_space_emax_EDF_h`, `refine_total_rbf`, `refine_task_eqdef`) are not public declarations; the
section's operation classes are instance binders and its `Context {eq_of2 : eq_of task_T}` is a named instance
binder, each definition taking only those it uses, in the order of the elaborated types; the section-local
`blocking_relevant` of `blocking_bound_NP_T` is inlined; `foldr +%C 0%C` is `List.foldr add_op zero_op`; `iota_T a Δ`
with `Δ : N` coerced to `nat` is `iota_T a (nat_of_bin Δ)`; `0` at `N` is `N.N0`; `flatten (map f s)` is
`(s.map f).flatten`; MathComp equality tests are `decide (x = y)`; the instances are those resolved in the source (the
latest declared, i.e. this file's `eq_NlistNN`/`eq_taskab`). -/

set_option linter.dupNamespace false
set_option warn.classDefReducibility false

namespace Prosa.Implementation.Refinements.EDF.Refinements

open Prosa.Behavior.Time
open Prosa.Util.Sum
open Prosa.Util.List
open Prosa.Model.Task.Concept
open Prosa.Model.Task.Arrival.Curves
open Prosa.Analysis.Definitions.RequestBoundFunction
open Prosa.Analysis.Definitions.BlockingBound.Edf
open Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve
open Prosa.Implementation.Definitions.ArrivalBound
open Prosa.Implementation.Definitions.Task
open Prosa.Implementation.Refinements.Refinements
open Prosa.Implementation.Refinements.ArrivalBound
open Prosa.Implementation.Refinements.Task
open Prosa.Implementation.Refinements.ArrivalCurve
open Prosa.Implementation.Refinements.EDF.FastSearchSpace

/-! ### Generic definitions -/

/-- Generic total request-bound function. -/
def total_rbf_T {T : Type} [zero_of T] [one_of T] [add_of T] [mul_of T] [div_of T] [mod_of T] [leq_of T]
    (ts : List (task_T T)) (Δ : T) : T :=
  let work_ts := ts.map (fun tsk' => task_rbf_T tsk' Δ)
  work_ts.foldr add_op zero_op

/-- Generic bound on the total higher-or-equal-priority workload. -/
def bound_on_total_hep_workload_T {T : Type} [zero_of T] [one_of T] [sub_of T] [add_of T] [mul_of T] [div_of T]
    [mod_of T] [leq_of T] [lt_of T] [eq_of2 : eq_of (task_T T)]
    (ts : List (task_T T)) (tsk : task_T T) (A Δ : T) : T :=
  let o_ts := ts.filter (fun tsk_o => !(eq_of2.eq_op tsk_o tsk))
  let o_work := o_ts.map (fun tsk_o => task_rbf_T tsk_o
    (minn_T (sub_op (add_op (add_op A one_op) (task_T.task_deadline_T tsk)) (task_T.task_deadline_T tsk_o)) Δ))
  o_work.foldr add_op zero_op

/-- Generic check of a point under the fully-preemptive policy. -/
def check_point_FP_T {T : Type} [zero_of T] [one_of T] [sub_of T] [add_of T] [mul_of T] [div_of T] [mod_of T]
    [leq_of T] [lt_of T] [eq_of2 : eq_of (task_T T)]
    (ts : List (task_T T)) (tsk : task_T T) (R : T) (P : T × T) : Bool :=
  leq_op (add_op (task_rbf_T tsk (add_op P.1 one_op)) (bound_on_total_hep_workload_T ts tsk P.1 (add_op P.1 P.2)))
      (add_op P.1 P.2) &&
    leq_op P.2 R

/-- Generic blocking bound under nonpreemptive policies. -/
def blocking_bound_NP_T {T : Type} [zero_of T] [one_of T] [sub_of T] [add_of T] [mul_of T] [div_of T] [mod_of T]
    [leq_of T] [lt_of T] (ts : List (task_T T)) (tsk : task_T T) (A : T) : T :=
  let ts_lp := ts.filter (fun tsk_o =>
    (lt_op zero_op (ConcreteMaxArrivals_T tsk_o one_op) && lt_op zero_op (task_T.task_cost_T tsk_o)) &&
      lt_op (add_op (task_T.task_deadline_T tsk) A) (task_T.task_deadline_T tsk_o))
  let ts_block := ts_lp.map (fun tsk_o => sub_op (task_T.task_cost_T tsk_o) one_op)
  ts_block.foldr maxn_T zero_op

/-- Generic check of a point under the fully-nonpreemptive policy. -/
def check_point_NP_T {T : Type} [zero_of T] [one_of T] [sub_of T] [add_of T] [mul_of T] [div_of T] [mod_of T]
    [leq_of T] [lt_of T] [eq_of2 : eq_of (task_T T)]
    (ts : List (task_T T)) (tsk : task_T T) (R : T) (P : T × T) : Bool :=
  leq_op (add_op (add_op (blocking_bound_NP_T ts tsk P.1)
      (sub_op (task_rbf_T tsk (add_op P.1 one_op)) (sub_op (task_T.task_cost_T tsk) one_op)))
      (bound_on_total_hep_workload_T ts tsk P.1 (add_op P.1 P.2))) (add_op P.1 P.2) &&
    leq_op (add_op P.2 (sub_op (task_T.task_cost_T tsk) one_op)) R

/-- A valid generic arrival bound. -/
def valid_arrivals_T {T : Type} [zero_of T] [one_of T] [eq_of T] [leq_of T] [lt_of T] (tsk : task_T T) : Bool :=
  match task_T.task_arrival_T tsk with
  | .Periodic_T p => leq_op one_op p
  | .Sporadic_T m => leq_op one_op m
  | .ArrivalPrefix_T emax_vec => valid_extrapolated_arrival_curve_T emax_vec

/-! ### Definitions at the binary numbers -/

/-- `iota` at `N`. -/
def iota_N (a Δ : N) : List N := iota_T a (nat_of_bin Δ)

/-- The binary search space of `tsk` induced by `tsko` in `[l * h, r * h)`. -/
def task_search_space_emax_EDF_h_N (tsk tsko : task_T N) (l r : N) : List N :=
  let h := get_horizon_of_task_T tsko
  let offsets := (iota_N l r).map (fun i => N.mul h i)
  let emax_offsets := repeat_steps_with_offset_T tsko offsets
  let emax_edf_offsets :=
    shift_points_neg_T (shift_points_pos_T emax_offsets (task_T.task_deadline_T tsko)) (task_T.task_deadline_T tsk)
  emax_edf_offsets.map predn_T

/-- The binary search space of `tsk` induced by `tsko`. -/
def task_search_space_emax_EDF_N (tsk tsko : task_T N) (L : N) : List N :=
  let h := get_horizon_of_task_T tsko
  task_search_space_emax_EDF_h_N tsk tsko N.N0
    (add_op (div_op (add_op L (sub_op (task_T.task_deadline_T tsk) (task_T.task_deadline_T tsko))) h) one_op)

/-- The binary search space. -/
def search_space_emax_EDF_N (ts : List (task_T N)) (tsk : task_T N) (L : N) : List N :=
  let points := ts.map (fun tsko => task_search_space_emax_EDF_N tsk tsko L)
  points.flatten

/-! ### Equality instances -/

/-- MathComp equality on lists of binary numbers. -/
instance eq_listN : eq_of (List N) := ⟨fun x y => decide (x = y)⟩

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

private theorem cma_N (tsk : task_T N) (d : N) :
    concrete_max_arrivals (taskT_to_task tsk) (nat_of_bin d) = nat_of_bin (ConcreteMaxArrivals_T tsk d) :=
  (Rnat_eq ((refine_ConcreteMaxArrivals' tsk).refines_rel _ d (Rnat_intro rfl))).symm

private theorem deadline_N (tsk : task_T N) :
    task_deadline (taskT_to_task tsk) = nat_of_bin (task_T.task_deadline_T tsk) := by
  obtain ⟨_, _, _, _, _⟩ := tsk; rfl

private theorem cost_N (tsk : task_T N) : task_cost (taskT_to_task tsk) = nat_of_bin (task_T.task_cost_T tsk) := by
  obtain ⟨_, _, _, _, _⟩ := tsk; rfl

private theorem horizon_N (tsk : task_T N) :
    get_horizon_of_task (taskT_to_task tsk) = nat_of_bin (get_horizon_of_task_T tsk) :=
  (Rnat_eq (refine_get_horizon_of_task.refines_rel _ tsk ⟨rfl⟩)).symm

private def list_R_Rtask_map : ∀ ts : List (task_T N), list_R Rtask (ts.map taskT_to_task) ts
  | [] => .nil_R
  | _ :: ts => .cons_R ⟨rfl⟩ (list_R_Rtask_map ts)

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

private theorem task_neq_N (t1 t2 : task_T N) :
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

private theorem task_search_space_N (tsk tsko : task_T N) (l r : N) :
    task_search_space_emax_EDF_h (taskT_to_task tsk) (taskT_to_task tsko) (nat_of_bin l) (nat_of_bin r) =
      (task_search_space_emax_EDF_h_N tsk tsko l r).map nat_of_bin := by
  symm
  apply list_R_Rnat_eq
  simp only [task_search_space_emax_EDF_h, task_search_space_emax_EDF_h_N, iota_N]
  refine list_R_map (fun x x' Rx => Rnat_pred.refines_rel x x' Rx) ?_
  refine refine_shift_points_neg.refines_rel _ _ ?_ _ _ (Rnat_intro (deadline_N tsk).symm)
  refine refine_shift_points_pos.refines_rel _ _ ?_ _ _ (Rnat_intro (deadline_N tsko).symm)
  refine refine_repeat_steps_with_offset.refines_rel _ tsko ⟨rfl⟩ _ _ ?_
  refine list_R_map (rA := Rnat) (fun x x' Rx => Rnat_intro ?_) ?_
  · show nat_of_bin (N.mul (get_horizon_of_task_T tsko) x') = get_horizon_of_task (taskT_to_task tsko) * x
    rw [nat_of_bin_mul, horizon_N, Rnat_eq Rx]
  · exact refine_iota.go _ _ _ (Rnat_intro rfl)

/-! ### Refinements -/

/-- Refinement of the search space of `tsk` induced by `tsko`. -/
def refine_task_search_space_emax_EDF :
    ∀ tsk tsko : task_T N,
      refines (hrespectful Rnat (list_R Rnat))
        (task_search_space_emax_EDF (taskT_to_task tsk) (taskT_to_task tsko)) (task_search_space_emax_EDF_N tsk tsko) :=
  fun tsk tsko => ⟨fun δ δ' Rδ => by
    have hb : (δ + (task_deadline (taskT_to_task tsk) - task_deadline (taskT_to_task tsko))) /
          get_horizon_of_task (taskT_to_task tsko) + 1 =
        nat_of_bin (add_op (div_op (add_op δ' (sub_op (task_T.task_deadline_T tsk) (task_T.task_deadline_T tsko)))
          (get_horizon_of_task_T tsko)) one_op) := by
      rw [nat_of_bin_add_op, nat_of_bin_div_op, nat_of_bin_add_op, nat_of_bin_sub_op, nat_of_bin_one, Rnat_eq Rδ,
        deadline_N, deadline_N, horizon_N]
    simp only [task_search_space_emax_EDF, task_search_space_emax_EDF_N]
    rw [hb, show (0 : Nat) = nat_of_bin N.N0 from rfl, task_search_space_N]
    exact list_R_Rnat_of_eq _⟩

/-- Refinement of the search space. -/
def refine_search_space_emax_EDF :
    ∀ (ts : List (task_T N)) (tsk : task_T N),
      refines (hrespectful Rnat (list_R Rnat))
        (search_space_emax_EDF (ts.map taskT_to_task) (taskT_to_task tsk)) (search_space_emax_EDF_N ts tsk) :=
  fun ts tsk => ⟨fun δ δ' Rδ => by
    have hone : ∀ tsko : task_T N,
        task_search_space_emax_EDF (taskT_to_task tsk) (taskT_to_task tsko) δ =
          (task_search_space_emax_EDF_N tsk tsko δ').map nat_of_bin := fun tsko =>
      (list_R_Rnat_eq ((refine_task_search_space_emax_EDF tsk tsko).refines_rel δ δ' Rδ)).symm
    have h : search_space_emax_EDF (ts.map taskT_to_task) (taskT_to_task tsk) δ =
        (search_space_emax_EDF_N ts tsk δ').map nat_of_bin := by
      simp only [search_space_emax_EDF, search_space_emax_EDF_N, Prosa.Util.Bigcat.bigCatSeqAll]
      induction ts with
      | nil => rfl
      | cons tsko ts ih =>
          simp only [List.map_cons, List.flatMap_cons, List.flatten_cons, List.map_append, ih, hone]
    rw [h]
    exact list_R_Rnat_of_eq _⟩

/-- Refinement of the total request-bound function, at converted tasks. -/
def refine_total_rbf' :
    ∀ ts : List (task_T N),
      refines (hrespectful Rnat Rnat) (total_request_bound_function (ts.map taskT_to_task)) (total_rbf_T ts) :=
  fun ts => ⟨fun Δ Δ' RΔ => (refine_uncond_foldr (ts.map taskT_to_task) ts
    (fun o => task_request_bound_function o Δ) (fun o => task_rbf_T o Δ') Rtask ⟨list_R_Rtask_map ts⟩
    ⟨fun o o' Ro => refine_task_rbf.refines_rel o o' Ro Δ Δ' RΔ⟩).refines_rel⟩

/-- Refinement of the bound on the total higher-or-equal-priority workload. -/
def refine_bound_on_total_hep_workload :
    refines (hrespectful (list_R Rtask) (hrespectful Rtask (hrespectful Rnat (hrespectful Rnat Rnat))))
      bound_on_total_hep_workload bound_on_total_hep_workload_T :=
  ⟨fun ts ts' Rts tsk tsk' Rtsk A A' RA Δ Δ' RΔ =>
    (refine_foldr ts ts' (fun o => decide (o ≠ tsk)) (fun o => !(eq_task.eq_op o tsk' : Bool))
      (fun o => task_rbf o (min (A + 1 + task_deadline tsk - task_deadline o) Δ))
      (fun o => task_rbf_T o (minn_T (sub_op (add_op (add_op A' one_op) (task_T.task_deadline_T tsk'))
        (task_T.task_deadline_T o)) Δ')) Rtask ⟨Rts⟩
      ⟨fun o o' Ro => refine_task_rbf.refines_rel o o' Ro _ _
        (refine_minn.refines_rel _ _ (Rnat_intro (by
          rw [nat_of_bin_sub_op, nat_of_bin_add_op, nat_of_bin_add_op, nat_of_bin_one, Rnat_eq RA, ← Rtsk.down,
            ← Ro.down, deadline_N, deadline_N])) _ _ RΔ)⟩
      ⟨fun o o' Ro => bool_R_of_eq (by rw [← Ro.down, ← Rtsk.down, task_neq_N])⟩).refines_rel⟩

private theorem botw_N {ts : List Prosa.Implementation.Refinements.Task.Task} {ts' : List (task_T N)}
    (Rts : list_R Rtask ts ts') {tsk : Prosa.Implementation.Refinements.Task.Task}
    {tsk' : task_T N} (Rtsk : Rtask tsk tsk') {A : Nat} {A' : N} (RA : Rnat A A') {Δ : Nat} {Δ' : N}
    (RΔ : Rnat Δ Δ') :
    nat_of_bin (bound_on_total_hep_workload_T ts' tsk' A' Δ') = bound_on_total_hep_workload ts tsk A Δ :=
  Rnat_eq (refine_bound_on_total_hep_workload.refines_rel ts ts' Rts tsk tsk' Rtsk A A' RA Δ Δ' RΔ)

/-- Refinement of the fully-preemptive check of a point. -/
def refine_check_point_FP :
    refines (hrespectful (list_R Rtask) (hrespectful Rtask (hrespectful Rnat (hrespectful (prod_R Rnat Rnat) bool_R))))
      check_point_FP check_point_FP_T :=
  ⟨fun ts ts' Rts tsk tsk' Rtsk R R' RR P P' RP => bool_R_of_eq (by
    obtain ⟨a, f⟩ := P
    obtain ⟨a', f'⟩ := P'
    cases RP with
    | pair_R Ra Rf =>
      have h1 : nat_of_bin (task_rbf_T tsk' (add_op a' one_op)) = task_rbf tsk (a + 1) := by
        rw [← Rtsk.down, ← task_rbf_N, nat_of_bin_add_op, nat_of_bin_one, Rnat_eq Ra]
      have h2 := botw_N Rts Rtsk Ra (Δ := a + f) (Δ' := add_op a' f')
        (Rnat_intro (by rw [nat_of_bin_add_op, Rnat_eq Ra, Rnat_eq Rf]))
      simp only [check_point_FP, check_point_FP_T, leq_op_N, nat_of_bin_add_op, h1, h2, Rnat_eq Ra, Rnat_eq Rf,
        Rnat_eq RR])⟩

/-- Refinement of the fully-preemptive check of a point, at converted tasks. -/
def refine_check_point_FP' :
    ∀ (ts : List (task_T N)) (tsk : task_T N),
      refines (hrespectful Rnat (hrespectful (prod_R Rnat Rnat) bool_R))
        (check_point_FP (ts.map taskT_to_task) (taskT_to_task tsk)) (check_point_FP_T ts tsk) :=
  fun ts tsk => ⟨fun R R' RR P P' RP =>
    refine_check_point_FP.refines_rel _ ts (list_R_Rtask_map ts) _ tsk ⟨rfl⟩ R R' RR P P' RP⟩

/-- Refinement of the blocking bound. -/
def refine_blocking_bound :
    refines (hrespectful (list_R Rtask) (hrespectful Rtask (hrespectful Rnat Rnat))) blocking_bound_NP blocking_bound_NP_T :=
  ⟨fun ts ts' Rts tsk tsk' Rtsk A A' RA => by
    have Rts' : list_R Rtask (ts.map (fun i => i)) ts' := by rw [List.map_id']; exact Rts
    exact (refine_foldr_max (ts.map (fun i => i)) ts'
      (fun o => blocking_relevant o && decide (task_deadline tsk + A < task_deadline o))
      (fun o => (lt_op zero_op (ConcreteMaxArrivals_T o one_op) && lt_op zero_op (task_T.task_cost_T o)) &&
        lt_op (add_op (task_T.task_deadline_T tsk') A') (task_T.task_deadline_T o))
      (fun o => task_cost o - 1) (fun o => sub_op (task_T.task_cost_T o) one_op) Rtask ⟨Rts'⟩
      ⟨fun o o' Ro => Rnat_intro (by rw [← Ro.down, nat_of_bin_sub_op, nat_of_bin_one, cost_N])⟩
      ⟨fun o o' Ro => bool_R_of_eq (by
        rw [← Ro.down, ← Rtsk.down]
        simp only [blocking_relevant, lt_op_N, nat_of_bin_add_op, nat_of_bin_zero, Rnat_eq RA, deadline_N, cost_N]
        rw [show max_arrivals (taskT_to_task o') 1 = concrete_max_arrivals (taskT_to_task o') (nat_of_bin one_op)
          from rfl, cma_N]
        try rfl)⟩).refines_rel⟩

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
      have h2 := botw_N Rts Rtsk Ra (Δ := a + f) (Δ' := add_op a' f')
        (Rnat_intro (by rw [nat_of_bin_add_op, Rnat_eq Ra, Rnat_eq Rf]))
      have h3 := Rnat_eq (refine_blocking_bound.refines_rel ts ts' Rts tsk tsk' Rtsk a a' Ra)
      have h4 : nat_of_bin (task_T.task_cost_T tsk') = task_cost tsk := by rw [← Rtsk.down, cost_N]
      simp only [check_point_NP, check_point_NP_T, leq_op_N, nat_of_bin_add_op, nat_of_bin_sub_op, nat_of_bin_one,
        h1, h2, h3, h4, Rnat_eq Ra, Rnat_eq Rf, Rnat_eq RR])⟩

/-- Refinement of the fully-nonpreemptive check of a point, at converted tasks. -/
def refine_check_point_NP' :
    ∀ (ts : List (task_T N)) (tsk : task_T N),
      refines (hrespectful Rnat (hrespectful (prod_R Rnat Rnat) bool_R))
        (check_point_NP (ts.map taskT_to_task) (taskT_to_task tsk)) (check_point_NP_T ts tsk) :=
  fun ts tsk => ⟨fun R R' RR P P' RP =>
    refine_check_point_NP.refines_rel _ ts (list_R_Rtask_map ts) _ tsk ⟨rfl⟩ R R' RR P P' RP⟩

end Prosa.Implementation.Refinements.EDF.Refinements
