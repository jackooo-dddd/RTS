-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/jitter/bertogna_edf_comp.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 182)

import Prosa.Classic.Util.All
import Prosa.Classic.Analysis.Global.Jitter.BertognaEdfTheory

/-!
Fixed-point iteration for Bertogna and Cirinei's global EDF response-time analysis with release jitter (Rocq module
`ResponseTimeIterationEDF` of `classic/analysis/global/jitter/bertogna_edf_comp.v`).

Representation notes:
* `task_with_response_time := (sporadic_task * time)%type` is `sporadic_task × time`; the section-local `Let`s `I`,
  `f`, `response_time_bounded_by` are unfolded, while `initial_state`, `max_steps`, `all_le` and `one_lt` are kept
  as `LEAN_HELPER` definitions of the same names (`all_le`/`one_lt` take only the section type, as the Rocq
  lemmas `all_le_reflexive`/`all_le_transitive` do).
* MathComp `iter` is the accepted `Prosa.Classic.Util.Fixedpoint.iter`; `unzip1 s` is `s.map Prod.fst`; `zip` is
  `List.zip`; `all`/`has` are `List.all`/`List.any`; `\sum_(tsk <- ts) F` is `Prosa.Util.Sum.sumSeq ts F`;
  `let (tsk, R) := pair in …` is a `match`; `o != None` is `!decide (o = none)`; `x \In A` is the accepted classic
  `optIn x A` (as `= true`); `a != b` in proposition position is `(!decide (a = b)) = true`; MathComp
  `reflexive R`/`transitive R` are stated pointwise (`∀ x, R x x`, `∀ y x z, R x y → R y z → R x z`); the motive
  `P : seq task_with_response_time -> Type` of `bertogna_edf_comp_iteration_inductive` is `… → Sort w`.
* In the `Convergence` section the task set is a sequence; in `MainProof` it is a `taskset_of sporadic_task` (the
  accepted `Prosa.Util.Seqset.set`), used as `ts.val` where the Rocq source coerces it to a sequence.
* Binder lists follow the Rocq contract. The convergence proofs use the pointwise relation `List.Forall₂` (through
  the LEAN_HELPER characterisation `all_le_iff`) instead of the index-based `zipP`/`nth` reasoning of the Rocq
  script; the argument (monotone iteration, strictly increasing sum of slacks bounded by `max_steps`) is the same.
  The main theorem is, as in Rocq, a direct application of the jitter-aware `bertogna_cirinei_response_time_bound_edf`
  (`Prosa.Classic.Analysis.Global.Jitter.BertognaEdfTheory`), using `edf_claimed_bounds_converges` for the
  fixed-point hypothesis.
* This module follows the translation of `classic/analysis/global/basic/bertogna_edf_comp.v`, with `task_jitter`
  threaded through the iteration, `jitter_plus_R_le_deadline` in place of `R_le_deadline`, the section-local
  `interference_bound_edf_monotonic` of the Rocq module (proved as in the jitter interference-bound translation), and an
  implicit `arr_seq` (a Rocq `Context`). The section-local `Let`s `no_deadline_missed_by_task`/`_job` are kept as
  `LEAN_HELPER` definitions of the same names.
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Jitter.BertognaEdfComp.ResponseTimeIterationEDF

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule hiding pending backlogged scheduled_implies_pending
open Prosa.Classic.Model.Schedule.Global.Jitter.Job.JobWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Jitter.Platform.Platform
open Prosa.Classic.Analysis.Global.Jitter.InterferenceBoundEdf.InterferenceBoundEDFJitter hiding interference_bound_edf_monotonic
open Prosa.Classic.Analysis.Global.Jitter.InterferenceBound.InterferenceBoundJitter
open Prosa.Classic.Analysis.Global.Jitter.WorkloadBound.WorkloadBoundJitter
open Prosa.Classic.Analysis.Global.Jitter.BertognaEdfTheory.ResponseTimeAnalysisEDFJitter
open Prosa.Classic.Util.DivMod (div_floor)
open Prosa.Classic.Util.Fixedpoint (iter iter_fix)
open Prosa.Classic.Util.Notation (optIn)
open Prosa.Util.Sum (sumSeq sumFiltered)

universe u v w

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def edf_response_time_bound {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (rt_bounds : List (sporadic_task × time)) (tsk : sporadic_task) (delta : time) : Nat :=
  task_cost tsk +
    div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds delta) num_cpus

def jitter_plus_R_le_deadline {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_deadline task_jitter : sporadic_task → time) (pair : sporadic_task × time) : Bool :=
  match pair with
  | (tsk, R) => decide (task_jitter tsk + R ≤ task_deadline tsk)

def update_bound {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (rt_bounds : List (sporadic_task × time)) (pair : sporadic_task × time) : sporadic_task × time :=
  match pair with
  | (tsk, R) => (tsk, edf_response_time_bound task_cost task_period task_deadline task_jitter num_cpus rt_bounds tsk R)

/-- LEAN_HELPER (Rocq `Let initial_state`). -/
def initial_state {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost : sporadic_task → time)
    (ts : List sporadic_task) : List (sporadic_task × time) :=
  ts.map (fun t => (t, task_cost t))

def edf_rta_iteration {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (rt_bounds : List (sporadic_task × time)) : List (sporadic_task × time) :=
  rt_bounds.map (update_bound task_cost task_period task_deadline task_jitter num_cpus rt_bounds)

/-- LEAN_HELPER (Rocq `Let max_steps`). -/
def max_steps {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline : sporadic_task → time)
    (ts : List sporadic_task) : Nat :=
  sumSeq ts (fun tsk => task_deadline tsk - task_cost tsk) + 1

def edf_claimed_bounds {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task) :
    Option (List (sporadic_task × time)) :=
  let R_values := iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)
  if R_values.all (jitter_plus_R_le_deadline task_deadline task_jitter) then some R_values else none

def edf_schedulable {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task) : Bool :=
  !decide (edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = none)

/-! ### Simple lemmas -/

theorem edf_claimed_bounds_unzip1_update_bound {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (l rt_bounds : List (sporadic_task × time)) :
    (l.map (update_bound task_cost task_period task_deadline task_jitter num_cpus rt_bounds)).map Prod.fst = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons p l IH =>
    obtain ⟨t, R⟩ := p
    simp only [List.map_cons, IH]
    rfl

theorem edf_claimed_bounds_unzip1_iteration {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (l : List sporadic_task) (k : Nat) :
    (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost l)).map Prod.fst = l := by
  induction k with
  | zero =>
    show (initial_state task_cost l).map Prod.fst = l
    unfold initial_state
    clear num_cpus
    induction l with
    | nil => rfl
    | cons a l ih => simp only [List.map_cons, ih]
  | succ k IH =>
    exact (edf_claimed_bounds_unzip1_update_bound task_cost task_period task_deadline task_jitter num_cpus _ _).trans IH

theorem edf_claimed_bounds_size {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (l : List sporadic_task) (k : Nat) :
    (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost l)).length = l.length := by
  have := congrArg List.length
    (edf_claimed_bounds_unzip1_iteration task_cost task_period task_deadline task_jitter num_cpus l k)
  rwa [List.length_map] at this

theorem edf_claimed_bounds_ge_cost {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (l : List sporadic_task) (k : Nat) (tsk : sporadic_task) (R : time) :
    (tsk, R) ∈ iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost l) → task_cost tsk ≤ R := by
  intro IN
  cases k with
  | zero =>
    change (tsk, R) ∈ initial_state task_cost l at IN
    obtain ⟨t, _, EQ⟩ := List.mem_map.mp IN
    simp only [Prod.mk.injEq] at EQ
    obtain ⟨rfl, rfl⟩ := EQ
    exact Nat.le_refl _
  | succ k =>
    change (tsk, R) ∈ edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost l)) at IN
    obtain ⟨⟨t, R0⟩, _, EQ⟩ := List.mem_map.mp IN
    simp only [update_bound, Prod.mk.injEq] at EQ
    obtain ⟨rfl, rfl⟩ := EQ
    exact Nat.le_add_right _ _

/-- LEAN_HELPER: the computed list is the state of the iteration after `max_steps` steps. -/
private theorem claimed_eq {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts : List sporadic_task) (rt_bounds : List (sporadic_task × time))
    (SOME : edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds) :
    rt_bounds = iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) ∧
      (iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)).all (jitter_plus_R_le_deadline task_deadline task_jitter) = true := by
  unfold edf_claimed_bounds at SOME
  simp only at SOME
  split at SOME
  · next ALL => exact ⟨(Option.some.inj SOME).symm, ALL⟩
  · exact absurd SOME (by simp)

theorem edf_claimed_bounds_le_deadline {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts : List sporadic_task) (rt_bounds : List (sporadic_task × time)) (tsk : sporadic_task) (R : time) :
    edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
    (tsk, R) ∈ rt_bounds →
    task_jitter tsk + R ≤ task_deadline tsk := by
  intro SOME IN
  obtain ⟨rfl, ALL⟩ := claimed_eq task_cost task_period task_deadline task_jitter num_cpus ts rt_bounds SOME
  exact of_decide_eq_true (List.all_eq_true.mp ALL _ IN)

theorem edf_claimed_bounds_has_R_for_every_task {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts : List sporadic_task) (rt_bounds : List (sporadic_task × time)) (tsk : sporadic_task) :
    edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
    tsk ∈ ts →
    ∃ R, (tsk, R) ∈ rt_bounds := by
  intro SOME IN
  obtain ⟨rfl, _⟩ := claimed_eq task_cost task_period task_deadline task_jitter num_cpus ts rt_bounds SOME
  rw [← edf_claimed_bounds_unzip1_iteration task_cost task_period task_deadline task_jitter num_cpus ts
    (max_steps task_cost task_deadline ts)] at IN
  obtain ⟨⟨t, R⟩, INp, EQ⟩ := List.mem_map.mp IN
  simp only at EQ
  subst EQ
  exact ⟨R, INp⟩

/-! ### Convergence -/

/-- LEAN_HELPER (Rocq `Let all_le`). -/
def all_le {sporadic_task : Type u} [DecidableEq sporadic_task] (l1 l2 : List (sporadic_task × time)) : Bool :=
  decide (l1.map Prod.fst = l2.map Prod.fst) && (l1.zip l2).all (fun p => decide (p.1.2 ≤ p.2.2))

/-- LEAN_HELPER (Rocq `Let one_lt`). -/
def one_lt {sporadic_task : Type u} [DecidableEq sporadic_task] (l1 l2 : List (sporadic_task × time)) : Bool :=
  decide (l1.map Prod.fst = l2.map Prod.fst) && (l1.zip l2).any (fun p => decide (p.1.2 < p.2.2))

/-- LEAN_HELPER: `all_le` is the pointwise relation "same task, no smaller bound". -/
private theorem all_le_iff {sporadic_task : Type u} [DecidableEq sporadic_task] :
    ∀ l1 l2 : List (sporadic_task × time),
      all_le l1 l2 = true ↔ List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) l1 l2
  | [], [] => by simp [all_le]
  | [], _ :: _ => by simp [all_le]
  | _ :: _, [] => by simp [all_le]
  | a :: l1, b :: l2 => by
    have IH := all_le_iff l1 l2
    unfold all_le at IH ⊢
    simp only [List.map_cons, List.cons.injEq, List.zip_cons_cons, List.all_cons, Bool.and_eq_true,
      decide_eq_true_eq, List.forall₂_cons] at IH ⊢
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨⟨h1, h3⟩, IH.mp ⟨h2, h4⟩⟩
    · rintro ⟨⟨h1, h3⟩, h⟩
      obtain ⟨h2, h4⟩ := IH.mpr h
      exact ⟨⟨h1, h2⟩, h3, h4⟩

/-- LEAN_HELPER: transitivity of the pointwise relation. -/
private theorem forall2_trans {α : Type u} :
    ∀ {l1 l2 l3 : List (α × time)},
      List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) l1 l2 →
      List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) l2 l3 →
      List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) l1 l3
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons ⟨h1.1.trans h2.1, Nat.le_trans h1.2 h2.2⟩ (forall2_trans t1 t2)

theorem all_le_reflexive {sporadic_task : Type u} [DecidableEq sporadic_task] :
    ∀ x : List (sporadic_task × time), all_le x x = true := by
  intro x
  rw [all_le_iff]
  induction x with
  | nil => exact .nil
  | cons a x IH => exact .cons ⟨rfl, Nat.le_refl _⟩ IH

theorem all_le_transitive {sporadic_task : Type u} [DecidableEq sporadic_task] :
    ∀ y x z : List (sporadic_task × time), all_le x y = true → all_le y z = true → all_le x z = true := by
  intro y x z H1 H2
  rw [all_le_iff] at H1 H2 ⊢
  exact forall2_trans H1 H2

/-- LEAN_HELPER: a list with the tasks of `ts` and bounds no smaller than the costs dominates the initial state. -/
private theorem init_forall2 {sporadic_task : Type u} (cost : sporadic_task → time) :
    ∀ (ts : List sporadic_task) (l : List (sporadic_task × time)), l.map Prod.fst = ts →
      (∀ b ∈ l, cost b.1 ≤ b.2) →
      List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) (ts.map (fun t => (t, cost t))) l
  | _, [], h, _ => by subst h; exact .nil
  | ts, b :: l, h, H => by
    cases ts with
    | nil => simp at h
    | cons t ts =>
      simp only [List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact .cons ⟨rfl, H b List.mem_cons_self⟩
        (init_forall2 cost ts l h (fun b' hb' => H b' (List.mem_cons_of_mem _ hb')))

/-- LEAN_HELPER: the elements of a list dominating the initial state are tasks of `ts` with bounds no smaller
than their costs. -/
private theorem forall2_init_props {sporadic_task : Type u} (cost : sporadic_task → time) :
    ∀ (ts : List sporadic_task) (l : List (sporadic_task × time)),
      List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) (ts.map (fun t => (t, cost t))) l →
      ∀ a ∈ l, a.1 ∈ ts ∧ cost a.1 ≤ a.2
  | [], _, h, a, ha => by
    cases h
    simp at ha
  | t :: ts, l, h, a, ha => by
    cases h with
    | cons hb tl =>
      rename_i b l'
      rcases List.mem_cons.mp ha with rfl | ha'
      · obtain ⟨h1, h2⟩ := hb
        simp only at h1 h2
        exact ⟨by rw [← h1]; exact List.mem_cons_self, by rw [← h1]; exact h2⟩
      · obtain ⟨IN, LE⟩ := forall2_init_props cost ts l' tl a ha'
        exact ⟨List.mem_cons_of_mem _ IN, LE⟩

/-! ### Monotonicity of the interference bound -/

theorem interference_bound_edf_monotonic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (tsk tsk_other : sporadic_task)
    (H_period_positive : 0 < task_period tsk_other) (delta delta' R R' : time)
    (H_delta_monotonic : delta ≤ delta') (H_response_time_monotonic : R ≤ R')
    (H_cost_le_rt_bound : task_cost tsk_other ≤ R) :
    interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta (tsk_other, R) ≤
      interference_bound_edf task_cost task_period task_deadline task_jitter tsk delta' (tsk_other, R') := by
  have hW := W_monotonic task_cost task_period task_jitter tsk_other H_period_positive R R'
    H_cost_le_rt_bound H_response_time_monotonic delta delta' H_delta_monotonic
  unfold interference_bound_edf interference_bound_generic edf_specific_interference_bound
  apply min_le_min
  · exact min_le_min hW (by omega')
  · exact Nat.add_le_add_left (min_le_min (Nat.le_refl _) (by omega')) _

/-- LEAN_HELPER: one step of the filtered sum defining the EDF interference bound. -/
private theorem tib_cons {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (tsk : sporadic_task)
    (p : sporadic_task × time) (l : List (sporadic_task × time)) (d : time) :
    total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk (p :: l) d =
      (if different_task tsk p.1 = true then interference_bound_edf task_cost task_period task_deadline task_jitter tsk d p
        else 0) + total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk l d := by
  obtain ⟨t, R⟩ := p
  unfold total_interference_bound_edf sumFiltered
  rw [List.filter_cons]
  by_cases h : different_task tsk t = true
  · simp only [h, ↓reduceIte, List.map_cons, List.sum_cons]
  · simp only [h, ↓reduceIte, Bool.false_eq_true, Nat.zero_add]

/-- LEAN_HELPER: the EDF interference bound is monotone in the response-time bounds and the window. -/
private theorem tib_mono {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (tsk : sporadic_task) (d1 d2 : time)
    (hd : d1 ≤ d2) :
    ∀ (l1 l2 : List (sporadic_task × time)), List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) l1 l2 →
      (∀ a ∈ l1, 0 < task_period a.1 ∧ task_cost a.1 ≤ a.2) →
      total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk l1 d1 ≤
        total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk l2 d2
  | [], [], _, _ => Nat.le_refl _
  | a :: l1, b :: l2, .cons hab tl, H => by
    rw [tib_cons, tib_cons]
    obtain ⟨t, R1⟩ := a
    obtain ⟨t', R2⟩ := b
    obtain ⟨h1, h2⟩ := hab
    simp only at h1 h2
    subst h1
    obtain ⟨PER, COST⟩ := H (t, R1) List.mem_cons_self
    apply Nat.add_le_add _ (tib_mono task_cost task_period task_deadline task_jitter tsk d1 d2 hd l1 l2 tl
      (fun a ha => H a (List.mem_cons_of_mem _ ha)))
    simp only
    split
    · exact Prosa.Classic.Analysis.Global.Jitter.BertognaEdfComp.ResponseTimeIterationEDF.interference_bound_edf_monotonic task_cost task_period task_deadline task_jitter tsk t PER d1 d2 R1 R2 hd h2 COST
    · exact Nat.le_refl _

/-- LEAN_HELPER: elementwise comparison of two iteration steps. -/
private theorem update_forall2 {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (l1 l2 : List (sporadic_task × time))
    (MONO : ∀ t R1 R2, R1 ≤ R2 →
      edf_response_time_bound task_cost task_period task_deadline task_jitter num_cpus l1 t R1 ≤
        edf_response_time_bound task_cost task_period task_deadline task_jitter num_cpus l2 t R2) :
    ∀ (m1 m2 : List (sporadic_task × time)), List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) m1 m2 →
      List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2)
        (m1.map (update_bound task_cost task_period task_deadline task_jitter num_cpus l1))
        (m2.map (update_bound task_cost task_period task_deadline task_jitter num_cpus l2))
  | [], [], _ => .nil
  | a :: m1, b :: m2, .cons hab tl => by
    obtain ⟨t, R1⟩ := a
    obtain ⟨t', R2⟩ := b
    obtain ⟨h1, h2⟩ := hab
    simp only at h1 h2
    subst h1
    exact .cons ⟨rfl, MONO t R1 R2 h2⟩ (update_forall2 task_cost task_period task_deadline task_jitter num_cpus l1 l2 MONO m1 m2 tl)

theorem bertogna_edf_comp_iteration_preserves_minimum {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts) (step : Nat) :
    all_le (initial_state task_cost ts) (iter (step) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) = true := by
  rw [all_le_iff]
  exact init_forall2 task_cost ts _ (edf_claimed_bounds_unzip1_iteration task_cost task_period task_deadline task_jitter num_cpus ts step)
    (fun b hb => edf_claimed_bounds_ge_cost task_cost task_period task_deadline task_jitter num_cpus ts step b.1 b.2 hb)

def bertogna_edf_comp_iteration_inductive {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (P : List (sporadic_task × time) → Sort w) :
    P (initial_state task_cost ts) →
    (∀ k, P (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) → P (iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts))) →
    P (iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) :=
  fun P0 Pn => Nat.rec (motive := fun k => P (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts))) P0 Pn _

theorem bertogna_edf_comp_iteration_preserves_order {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts)
    (l1 l2 : List (sporadic_task × time)) :
    all_le (initial_state task_cost ts) l1 = true →
    all_le l1 l2 = true →
    all_le (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus l1)
      (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus l2) = true := by
  intro LEinit LE
  rw [all_le_iff] at LEinit LE ⊢
  have PROPS := forall2_init_props task_cost ts l1 LEinit
  apply update_forall2 task_cost task_period task_deadline task_jitter num_cpus l1 l2 _ l1 l2 LE
  intro t R1 R2 hR
  apply Nat.add_le_add_left
  apply Nat.div_le_div_right
  apply tib_mono task_cost task_period task_deadline task_jitter t R1 R2 hR l1 l2 LE
  intro a ha
  obtain ⟨IN, COST⟩ := PROPS a ha
  exact ⟨of_decide_eq_true (H_valid_task_parameters a.1 IN).2.1, COST⟩

theorem bertogna_edf_comp_iteration_monotonic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts) (k : Nat) :
    all_le (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) = true := by
  induction k with
  | zero =>
    exact bertogna_edf_comp_iteration_preserves_minimum task_cost task_period task_deadline task_jitter num_cpus ts
      H_valid_task_parameters 1
  | succ k ih =>
    exact bertogna_edf_comp_iteration_preserves_order task_cost task_period task_deadline task_jitter num_cpus ts
      H_valid_task_parameters _ _
      (bertogna_edf_comp_iteration_preserves_minimum task_cost task_period task_deadline task_jitter num_cpus ts
        H_valid_task_parameters k) ih

theorem bertogna_edf_comp_f_converges_with_no_tasks {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts) :
    ts.length = 0 →
    iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) = iter (max_steps task_cost task_deadline ts + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) := by
  intro SIZE
  have NIL : ts = [] := List.eq_nil_of_length_eq_zero SIZE
  have ALL : ∀ k, iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) = [] := by
    intro k
    induction k with
    | zero => show initial_state task_cost ts = []; rw [NIL]; rfl
    | succ k ih =>
      show edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) = []
      rw [ih]
      rfl
  rw [ALL, ALL]

theorem bertogna_edf_comp_f_converges_early {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task) :
    (∃ k, k ≤ max_steps task_cost task_deadline ts ∧ iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) = iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) →
    iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) = iter (max_steps task_cost task_deadline ts + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) := by
  rintro ⟨k, LE, EQ⟩
  exact iter_fix _ _ _ k _ EQ LE

/-- LEAN_HELPER: pointwise-related lists in which no bound increases are equal. -/
private theorem forall2_eq_of_not_any {α : Type u} :
    ∀ {l1 l2 : List (α × time)}, List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) l1 l2 →
      (l1.zip l2).any (fun p => decide (p.1.2 < p.2.2)) = false → l1 = l2
  | _, _, .nil, _ => rfl
  | a :: _, b :: _, .cons hab tl, H => by
    simp only [List.zip_cons_cons, List.any_cons, Bool.or_eq_false_iff, decide_eq_false_iff_not] at H
    obtain ⟨h1, h2⟩ := hab
    have hR : a.2 = b.2 := by omega'
    rw [forall2_eq_of_not_any tl H.2, Prod.ext h1 hR]

/-- LEAN_HELPER: summing a non-negative quantity over a list respects pointwise bounds. -/
private theorem sumSeq_le_of_le {α : Type u} (l : List α) (f g : α → Nat) (h : ∀ a ∈ l, f a ≤ g a) :
    sumSeq l f ≤ sumSeq l g := by
  unfold sumSeq
  induction l with
  | nil => exact Nat.le_refl _
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self) (ih (fun b hb => h b (List.mem_cons_of_mem _ hb)))

/-- LEAN_HELPER: the sum of slacks does not decrease along pointwise-related lists. -/
private theorem sum_le_of_forall2 {α : Type u} (cost : α → time) :
    ∀ {l1 l2 : List (α × time)}, List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) l1 l2 →
      sumSeq l1 (fun p => p.2 - cost p.1) ≤ sumSeq l2 (fun p => p.2 - cost p.1)
  | _, _, .nil => Nat.le_refl _
  | a :: l1, b :: l2, .cons hab tl => by
    have IH := sum_le_of_forall2 cost tl
    unfold sumSeq at *
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨h1, h2⟩ := hab
    rw [← h1]
    omega'

/-- LEAN_HELPER: the sum of slacks strictly increases along pointwise-related lists with one strict increase. -/
private theorem sum_lt_of_forall2 {α : Type u} (cost : α → time) :
    ∀ {l1 l2 : List (α × time)}, List.Forall₂ (fun a b => a.1 = b.1 ∧ a.2 ≤ b.2) l1 l2 →
      (∀ a ∈ l1, cost a.1 ≤ a.2) →
      (l1.zip l2).any (fun p => decide (p.1.2 < p.2.2)) = true →
      sumSeq l1 (fun p => p.2 - cost p.1) < sumSeq l2 (fun p => p.2 - cost p.1)
  | _, _, .nil, _, H => by simp at H
  | a :: l1, b :: l2, .cons hab tl, C, H => by
    have Ca := C a List.mem_cons_self
    have C' : ∀ x ∈ l1, cost x.1 ≤ x.2 := fun x hx => C x (List.mem_cons_of_mem _ hx)
    have LEsum := sum_le_of_forall2 cost tl
    simp only [List.zip_cons_cons, List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at H
    obtain ⟨h1, h2⟩ := hab
    rcases H with H | H
    · unfold sumSeq at *
      simp only [List.map_cons, List.sum_cons]
      rw [← h1]
      omega'
    · have LT := sum_lt_of_forall2 cost tl C' H
      unfold sumSeq at *
      simp only [List.map_cons, List.sum_cons]
      rw [← h1]
      omega'

theorem bertogna_edf_comp_f_increases {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts)
    (H_at_least_one_task : 0 < ts.length)
    (H_keeps_diverging : ∀ k, k ≤ max_steps task_cost task_deadline ts →
      (!decide (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) = iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts))) = true)
    (k : Nat) :
    k ≤ max_steps task_cost task_deadline ts → one_lt (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) = true := by
  intro LEk
  unfold one_lt
  rw [edf_claimed_bounds_unzip1_iteration, edf_claimed_bounds_unzip1_iteration]
  simp only [decide_true, Bool.true_and]
  have MONO := (all_le_iff _ _).mp
    (bertogna_edf_comp_iteration_monotonic task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters k)
  cases H : ((iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)).zip (iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts))).any (fun p => decide (p.1.2 < p.2.2))
  · exfalso
    have EQ := forall2_eq_of_not_any MONO H
    have DIFF := H_keeps_diverging k LEk
    rw [EQ] at DIFF
    simp at DIFF
  · rfl

theorem bertogna_edf_comp_rt_grows_too_much {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts)
    (H_at_least_one_task : 0 < ts.length)
    (H_keeps_diverging : ∀ k, k ≤ max_steps task_cost task_deadline ts →
      (!decide (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) = iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts))) = true)
    (k : Nat) :
    k ≤ max_steps task_cost task_deadline ts →
    k < sumSeq (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun (tsk, R) => R - task_cost tsk) + 1 := by
  induction k with
  | zero => intro _; exact Nat.succ_pos _
  | succ k ih =>
    intro LE
    have IH := ih (Nat.le_of_succ_le LE)
    have INC := bertogna_edf_comp_f_increases task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters
      H_at_least_one_task H_keeps_diverging k (Nat.le_of_succ_le LE)
    unfold one_lt at INC
    simp only [Bool.and_eq_true] at INC
    have MONO := (all_le_iff _ _).mp
      (bertogna_edf_comp_iteration_monotonic task_cost task_period task_deadline task_jitter num_cpus ts H_valid_task_parameters k)
    have LT := sum_lt_of_forall2 task_cost MONO
      (fun a ha => edf_claimed_bounds_ge_cost task_cost task_period task_deadline task_jitter num_cpus ts k a.1 a.2 ha) INC.2
    have E1 : sumSeq (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun (tsk, R) => R - task_cost tsk) =
        sumSeq (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun p => p.2 - task_cost p.1) := rfl
    have E2 : sumSeq (iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun (tsk, R) => R - task_cost tsk) =
        sumSeq (iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun p => p.2 - task_cost p.1) := rfl
    rw [E2]
    rw [E1] at IH
    omega'

theorem edf_claimed_bounds_finds_fixed_point_of_list {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts)
    (rt_bounds : List (sporadic_task × time)) :
    edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
    valid_sporadic_taskset task_cost task_period task_deadline ts →
    iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) =
      edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus (iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) := by
  intro SOME VALID
  obtain ⟨_, ALL⟩ := claimed_eq task_cost task_period task_deadline task_jitter num_cpus ts rt_bounds SOME
  by_cases EMPTY : ts.length = 0
  · exact bertogna_edf_comp_f_converges_with_no_tasks task_cost task_period task_deadline task_jitter num_cpus ts
      H_valid_task_parameters EMPTY
  by_cases EX : ∃ k, k ≤ max_steps task_cost task_deadline ts ∧ iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) = iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)
  · exact bertogna_edf_comp_f_converges_early task_cost task_period task_deadline task_jitter num_cpus ts EX
  exfalso
  have DIFF : ∀ k, k ≤ max_steps task_cost task_deadline ts → (!decide (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts) = iter (k + 1) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts))) = true := by
    intro k hk
    simp only [Bool.not_eq_true', decide_eq_false_iff_not]
    exact fun h => EX ⟨k, hk, h⟩
  have TOO := bertogna_edf_comp_rt_grows_too_much task_cost task_period task_deadline task_jitter num_cpus ts
    H_valid_task_parameters (Nat.pos_of_ne_zero EMPTY) DIFF _ (Nat.le_refl _)
  have UNZIP := edf_claimed_bounds_unzip1_iteration task_cost task_period task_deadline task_jitter num_cpus ts
    (max_steps task_cost task_deadline ts)
  have E1 : sumSeq (iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun (tsk, R) => R - task_cost tsk) =
      sumSeq (iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun p => p.2 - task_cost p.1) := rfl
  rw [E1] at TOO
  have SUM : sumSeq (iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun p => p.2 - task_cost p.1) ≤
      sumSeq ts (fun tsk => task_deadline tsk - task_cost tsk) := by
    calc sumSeq (iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun p => p.2 - task_cost p.1)
        ≤ sumSeq (iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) (fun p => task_deadline p.1 - task_cost p.1) := by
          apply sumSeq_le_of_le
          rintro ⟨t, R⟩ IN
          have := of_decide_eq_true (List.all_eq_true.mp ALL _ IN)
          show R - task_cost t ≤ task_deadline t - task_cost t
          omega'
      _ = sumSeq ts (fun tsk => task_deadline tsk - task_cost tsk) := by
          conv_rhs => rw [← UNZIP]
          unfold sumSeq
          rw [List.map_map]
          rfl
  have MS : max_steps task_cost task_deadline ts = sumSeq ts (fun tsk => task_deadline tsk - task_cost tsk) + 1 := rfl
  omega'

theorem edf_claimed_bounds_finds_least_fixed_point {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts)
    (v : List (sporadic_task × time)) :
    all_le (initial_state task_cost ts) v = true →
    v = edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus v →
    all_le (iter (max_steps task_cost task_deadline ts) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts)) v = true := by
  intro GE0 EQ
  apply bertogna_edf_comp_iteration_inductive task_cost task_period task_deadline task_jitter num_cpus ts
    (fun l => all_le l v = true) GE0
  intro k GEk
  show all_le (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus (iter (k) (edf_rta_iteration task_cost task_period task_deadline task_jitter num_cpus) (initial_state task_cost ts))) v = true
  rw [EQ]
  exact bertogna_edf_comp_iteration_preserves_order task_cost task_period task_deadline task_jitter num_cpus ts
    H_valid_task_parameters _ _
    (bertogna_edf_comp_iteration_preserves_minimum task_cost task_period task_deadline task_jitter num_cpus ts
      H_valid_task_parameters k) (EQ ▸ GEk)

theorem edf_claimed_bounds_finds_fixed_point_for_each_bound {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts)
    (tsk : sporadic_task) (R : time) (rt_bounds : List (sporadic_task × time)) :
    edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
    (tsk, R) ∈ rt_bounds →
    R = edf_response_time_bound task_cost task_period task_deadline task_jitter num_cpus rt_bounds tsk R := by
  intro SOME IN
  have CONV := edf_claimed_bounds_finds_fixed_point_of_list task_cost task_period task_deadline task_jitter num_cpus ts
    H_valid_task_parameters rt_bounds SOME H_valid_task_parameters
  obtain ⟨EQ, _⟩ := claimed_eq task_cost task_period task_deadline task_jitter num_cpus ts rt_bounds SOME
  rw [← EQ] at CONV
  obtain ⟨i, hi, hget⟩ := List.getElem_of_mem IN
  have E := congrArg (fun l => l[i]?) CONV
  unfold edf_rta_iteration at E
  rw [List.getElem?_map, List.getElem?_eq_getElem hi, hget] at E
  simp only [Option.map_some, Option.some.injEq, update_bound, Prod.mk.injEq] at E
  exact E.2

theorem edf_claimed_bounds_converges {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts)
    (tsk : sporadic_task) (R : time) (rt_bounds : List (sporadic_task × time)) :
    edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some rt_bounds →
    (tsk, R) ∈ rt_bounds →
    R = task_cost tsk +
      div_floor (total_interference_bound_edf task_cost task_period task_deadline task_jitter tsk rt_bounds R)
        num_cpus := by
  intro SOME IN
  exact edf_claimed_bounds_finds_fixed_point_for_each_bound task_cost task_period task_deadline task_jitter num_cpus
    ts H_valid_task_parameters tsk R rt_bounds SOME IN

/-! ### Main proof -/

/-- LEAN_HELPER (Rocq `Let no_deadline_missed_by_task`). -/
def no_deadline_missed_by_task {sporadic_task : Type u} {Job : Type v} [DecidableEq sporadic_task]
    [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task)
    (num_cpus : Nat) (arr_seq : arrival_sequence Job) (sched : schedule Job num_cpus) (tsk : sporadic_task) :
    Prop :=
  task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk

/-- LEAN_HELPER (Rocq `Let no_deadline_missed_by_job`). -/
def no_deadline_missed_by_job {Job : Type v} [DecidableEq Job] (job_arrival job_cost job_deadline : Job → time)
    (num_cpus : Nat) (sched : schedule Job num_cpus) (j : Job) : Bool :=
  job_misses_no_deadline job_arrival job_cost job_deadline sched j

theorem edf_analysis_yields_response_time_bounds
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (num_cpus : Nat)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    {arr_seq : arrival_sequence Job}
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (sched : schedule Job num_cpus)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    :
    ∀ (tsk : sporadic_task) (R : time),
      optIn (tsk, R) (edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts.val) = true →
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
  intro tsk R IN
  cases SOME : edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts.val with
  | none => rw [SOME] at IN; simp [optIn] at IN
  | some rt_bounds =>
    rw [SOME] at IN
    simp only [optIn, decide_eq_true_eq] at IN
    obtain ⟨EQ, _⟩ := claimed_eq task_cost task_period task_deadline task_jitter num_cpus ts.val rt_bounds SOME
    have UNZIP : rt_bounds.map Prod.fst = ts.val := by
      rw [EQ]; exact edf_claimed_bounds_unzip1_iteration task_cost task_period task_deadline task_jitter num_cpus ts.val _
    exact bertogna_cirinei_response_time_bound_edf task_cost task_period task_deadline task_jitter job_arrival
      job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence
      H_sequential_jobs H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_at_least_one_cpu
      H_work_conserving H_edf_policy rt_bounds UNZIP
      (fun t R0 h => edf_claimed_bounds_converges task_cost task_period task_deadline task_jitter
        num_cpus ts.val H_valid_task_parameters t R0 rt_bounds SOME h)
      (fun t R0 h => edf_claimed_bounds_le_deadline task_cost task_period task_deadline task_jitter num_cpus ts.val
        rt_bounds t R0 SOME h)
      tsk R IN

theorem taskset_schedulable_by_edf_rta
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (num_cpus : Nat)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    {arr_seq : arrival_sequence Job}
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (sched : schedule Job num_cpus)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (H_test_succeeds : edf_schedulable task_cost task_period task_deadline task_jitter num_cpus ts.val = true)
    :
    ∀ tsk, tsk ∈ ts →
      no_deadline_missed_by_task job_arrival job_cost job_deadline job_task num_cpus arr_seq sched tsk := by
  intro tsk INtsk j ARRj JOBtsk
  unfold edf_schedulable at H_test_succeeds
  cases SOME : edf_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts.val with
  | none => rw [SOME] at H_test_succeeds; simp at H_test_succeeds
  | some rt_bounds =>
    obtain ⟨R, INR⟩ := edf_claimed_bounds_has_R_for_every_task task_cost task_period task_deadline task_jitter
      num_cpus ts.val rt_bounds tsk SOME INtsk
    have DL := edf_claimed_bounds_le_deadline task_cost task_period task_deadline task_jitter num_cpus ts.val
      rt_bounds tsk R SOME INR
    have RESP := edf_analysis_yields_response_time_bounds task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter num_cpus ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks sched H_at_least_one_cpu H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_edf_policy tsk R (by rw [SOME]; simp [optIn, INR])
    have COMP := RESP j ARRj JOBtsk
    have JDL : job_deadline j = task_deadline (job_task j) := (H_valid_job_parameters j ARRj).1.2.2
    unfold job_misses_no_deadline
    apply completion_monotonic job_cost sched j _ _ _ COMP
    rw [JDL, JOBtsk]
    exact Nat.add_le_add_left DL _

theorem jobs_schedulable_by_edf_rta
    {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time)
    {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (num_cpus : Nat)
    (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    {arr_seq : arrival_sequence Job}
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (sched : schedule Job num_cpus)
    (H_at_least_one_cpu : 0 < num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_execute_after_jitter : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_edf_policy :
      respects_JLFP_policy job_arrival job_cost job_jitter arr_seq sched (EDF job_arrival job_deadline))
    (H_test_succeeds : edf_schedulable task_cost task_period task_deadline task_jitter num_cpus ts.val = true)
    :
    ∀ j, arrives_in arr_seq j → no_deadline_missed_by_job job_arrival job_cost job_deadline num_cpus sched j = true := by
  intro j ARRj
  exact taskset_schedulable_by_edf_rta task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter num_cpus ts H_valid_task_parameters H_constrained_deadlines H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks sched H_at_least_one_cpu H_jobs_come_from_arrival_sequence H_jobs_execute_after_jitter H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_edf_policy H_test_succeeds (job_task j) (H_all_jobs_from_taskset j ARRj) j ARRj rfl

end Prosa.Classic.Analysis.Global.Jitter.BertognaEdfComp.ResponseTimeIterationEDF
