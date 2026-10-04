-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/analysis/global/jitter/bertogna_fp_comp.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 173)

import Prosa.Classic.Util.All
import Prosa.Classic.Analysis.Global.Jitter.BertognaFpTheory

/-!
Fixed-point iteration for Bertogna and Cirinei's global FP response-time analysis with release jitter (Rocq module
`ResponseTimeIterationFP` of `classic/analysis/global/jitter/bertogna_fp_comp.v`).

Representation notes:
* `task_with_response_time := (sporadic_task * time)%type` is `sporadic_task × time` (the section-local `Let` is
  unfolded, as are `TASK`, `f`, `no_deadline_missed_by_task`, `no_deadline_missed_by_job` and
  `response_time_bounded_by`); MathComp's `iter` is the accepted `Prosa.Classic.Util.Fixedpoint.iter`.
* `rcons s x` is `s ++ [x]`; `foldl` is `List.foldl`; `unzip1 s` is `s.map Prod.fst`; `nth elem ts i` is
  `ts.val.getD i elem`; `if hp_pairs is Some rt_bounds then … else None` is a `match`; `o != None` is
  `!decide (o = none)`; `x \In A` is the accepted classic `optIn x A` (as `= true`); `a != b` in proposition position
  is `(!decide (a = b)) = true`.
* `sorted higher_priority ts` is `List.IsChain (fun a b => higher_priority a b = true) ts.val` (as in the accepted
  `Prosa.Classic.Util.Sorting`); a `taskset_of sporadic_task` is the accepted `Prosa.Util.Seqset.set` and is used as
  its underlying list `ts.val` where the Rocq source coerces it to a sequence.
* Binder lists follow the Rocq contract. The proof of `fp_analysis_yields_response_time_bounds` proceeds by induction
  on prefixes of the task set (rather than on indices, as in the Rocq script); the inductive step is, as in Rocq, the
  main theorem `bertogna_cirinei_response_time_bound_fp` of the jitter `bertogna_fp_theory` translation
  (`Prosa.Classic.Analysis.Global.Jitter.BertognaFpTheory`). This module follows the translation of
  `classic/analysis/global/basic/bertogna_fp_comp.v`, with the jitter-aware interference bound, the deadline test
  `task_jitter tsk + R <= task_deadline tsk`, response-time bounds `task_jitter tsk + R`, and the jitter-aware
  scheduler hypotheses (the Rocq hypothesis named `H_jobs_must_arrive_to_execute` states
  `jobs_execute_after_jitter`).
-/

set_option linter.dupNamespace false
set_option linter.unusedVariables false

namespace Prosa.Classic.Analysis.Global.Jitter.BertognaFpComp.ResponseTimeIterationFP

open Prosa.Classic.Model.Time.Time
open Prosa.Classic.Model.Arrival.Basic.ArrivalSequence.ArrivalSequence
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTaskset
open Prosa.Classic.Model.Arrival.Basic.Task.SporadicTask
open Prosa.Classic.Model.Arrival.Basic.Job.Job
open Prosa.Classic.Model.Arrival.Basic.TaskArrival.TaskArrival
open Prosa.Classic.Model.Priority.Priority
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.Schedule
open Prosa.Classic.Model.Schedule.Global.Basic.Schedule.ScheduleOfSporadicTask
open Prosa.Classic.Model.Schedule.Global.ResponseTime.ResponseTime
open Prosa.Classic.Model.Schedule.Global.Schedulability.Schedulability
open Prosa.Classic.Model.Schedule.Global.Jitter.Job.JobWithJitter
open Prosa.Classic.Model.Schedule.Global.Jitter.Schedule.ScheduleWithJitter (jobs_execute_after_jitter)
open Prosa.Classic.Model.Schedule.Global.Jitter.Platform.Platform
open Prosa.Classic.Analysis.Global.Jitter.WorkloadBound.WorkloadBoundJitter
open Prosa.Classic.Analysis.Global.Jitter.InterferenceBoundFp.InterferenceBoundFP
open Prosa.Classic.Analysis.Global.Jitter.BertognaFpTheory.ResponseTimeAnalysisFP
open Prosa.Classic.Util.DivMod (div_floor)
open Prosa.Classic.Util.Fixedpoint (iter iter_fix fun_mon_iter_mon)
open Prosa.Classic.Util.Sorting (sorted_rel_implies_le_idx)
open Prosa.Classic.Util.Notation (optIn)
open Prosa.Util.Sum (sumSeq)

universe u v

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def per_task_rta {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_period task_jitter : sporadic_task → time)
    (num_cpus : Nat) (tsk : sporadic_task) (R_prev : List (sporadic_task × time)) (step : Nat) : time :=
  iter step
    (fun t => task_cost tsk +
      div_floor (total_interference_bound_fp task_cost task_period task_jitter tsk R_prev t) num_cpus)
    (task_cost tsk)

def max_steps {sporadic_task : Type u} [DecidableEq sporadic_task] (task_cost task_deadline : sporadic_task → time)
    (tsk : sporadic_task) : Nat :=
  task_deadline tsk - task_cost tsk + 1

def fp_bound_of_task {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (hp_pairs : Option (List (sporadic_task × time))) (tsk : sporadic_task) : Option (List (sporadic_task × time)) :=
  match hp_pairs with
  | some rt_bounds =>
    let R := per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (max_steps task_cost task_deadline tsk)
    if task_jitter tsk + R ≤ task_deadline tsk then some (rt_bounds ++ [(tsk, R)]) else none
  | none => none

def fp_claimed_bounds {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task) :
    Option (List (sporadic_task × time)) :=
  ts.foldl (fp_bound_of_task task_cost task_period task_deadline task_jitter num_cpus) (some [])

def fp_schedulable {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (ts : List sporadic_task) : Bool :=
  !decide (fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = none)

/-! ### LEAN_HELPER lemmas -/

/-- LEAN_HELPER: one step of the left fold. -/
private theorem claimed_snoc {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (l : List sporadic_task)
    (t : sporadic_task) (B : List (sporadic_task × time))
    (H : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus (l ++ [t]) = some B) :
    ∃ hp, fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus l = some hp ∧
      task_jitter t + per_task_rta task_cost task_period task_jitter num_cpus t hp (max_steps task_cost task_deadline t) ≤
        task_deadline t ∧
      B = hp ++ [(t, per_task_rta task_cost task_period task_jitter num_cpus t hp (max_steps task_cost task_deadline t))] := by
  unfold fp_claimed_bounds at H ⊢
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil] at H
  cases h : l.foldl (fp_bound_of_task task_cost task_period task_deadline task_jitter num_cpus) (some []) with
  | none => rw [h] at H; simp [fp_bound_of_task] at H
  | some hp =>
    rw [h] at H
    simp only [fp_bound_of_task] at H
    split at H
    · next hle => exact ⟨hp, rfl, hle, (Option.some.inj H).symm⟩
    · exact absurd H (by simp)

/-- LEAN_HELPER: every computed pair is the result of the iteration and respects the deadline. -/
private theorem mem_claimed {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) :
    ∀ (l : List sporadic_task) (B : List (sporadic_task × time)),
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus l = some B →
      ∀ tsk R, (tsk, R) ∈ B →
        ∃ hp, R = per_task_rta task_cost task_period task_jitter num_cpus tsk hp (max_steps task_cost task_deadline tsk) ∧
          task_jitter tsk + R ≤ task_deadline tsk := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro B H tsk R IN
    simp only [fp_claimed_bounds, List.foldl_nil, Option.some.injEq] at H
    subst H; simp at IN
  | append_singleton l t IH =>
    intro B H tsk R IN
    obtain ⟨hp, Hl, LE, rfl⟩ := claimed_snoc task_cost task_period task_deadline task_jitter num_cpus l t B H
    rcases List.mem_append.mp IN with INhp | INlast
    · exact IH hp Hl tsk R INhp
    · simp only [List.mem_singleton, Prod.mk.injEq] at INlast
      obtain ⟨rfl, rfl⟩ := INlast
      exact ⟨hp, rfl, LE⟩

/-- LEAN_HELPER: the iteration never goes below the task cost. -/
private theorem per_task_rta_ge_cost {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_jitter : sporadic_task → time) (num_cpus : Nat) (tsk : sporadic_task)
    (R_prev : List (sporadic_task × time)) (step : Nat) :
    task_cost tsk ≤ per_task_rta task_cost task_period task_jitter num_cpus tsk R_prev step := by
  cases step with
  | zero => exact Nat.le_refl _
  | succ n => exact Nat.le_add_right _ _

/-- LEAN_HELPER: a chain of a transitive relation is pairwise related. -/
private theorem chain_pairwise {T : Type u} (R : T → T → Prop) (trans : ∀ y x z, R x y → R y z → R x z) :
    ∀ l : List T, List.IsChain R l → List.Pairwise R l
  | [], _ => List.Pairwise.nil
  | [_], _ => List.pairwise_singleton _ _
  | a :: b :: l, h => by
    have hab : R a b := List.IsChain.rel h
    have IH := chain_pairwise R trans (b :: l) (List.IsChain.tail h)
    refine List.Pairwise.cons ?_ IH
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact hab
    · exact trans b a c hab (List.rel_of_pairwise_cons IH hc)

/-! ### Simple lemmas about the computed list -/


theorem fp_claimed_bounds_unzip {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts : List sporadic_task) (hp_bounds : List (sporadic_task × time)) :
    fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some hp_bounds →
    hp_bounds.map Prod.fst = ts := by
  induction ts using List.reverseRecOn generalizing hp_bounds with
  | nil =>
    intro H
    simp only [fp_claimed_bounds, List.foldl_nil, Option.some.injEq] at H
    subst H; rfl
  | append_singleton l t IH =>
    intro H
    obtain ⟨hp, Hl, _, rfl⟩ := claimed_snoc task_cost task_period task_deadline task_jitter num_cpus l t hp_bounds H
    rw [List.map_append, IH hp Hl]
    rfl

theorem fp_claimed_bounds_rcons {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts' : List sporadic_task) (hp_bounds : List (sporadic_task × time)) (tsk1 tsk2 : sporadic_task) (R : time) :
    fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus (ts' ++ [tsk1]) =
        some (hp_bounds ++ [(tsk2, R)]) →
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts' = some hp_bounds ∧
      tsk1 = tsk2 ∧
      R = per_task_rta task_cost task_period task_jitter num_cpus tsk1 hp_bounds (max_steps task_cost task_deadline tsk1) ∧
      task_jitter tsk1 + R ≤ task_deadline tsk1 := by
  intro H
  obtain ⟨hp, Hl, LE, EQ⟩ := claimed_snoc task_cost task_period task_deadline task_jitter num_cpus ts' tsk1 _ H
  obtain ⟨E1, E2⟩ := List.append_inj' EQ rfl
  simp only [List.cons.injEq, Prod.mk.injEq, and_true] at E2
  obtain ⟨rfl, rfl⟩ := E2
  subst E1
  exact ⟨Hl, rfl, rfl, LE⟩

/-- LEAN_HELPER: the computation of a prefix is the corresponding prefix of the computation. -/
private theorem claimed_append {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat) (l1 : List sporadic_task) :
    ∀ (l2 : List sporadic_task) (B : List (sporadic_task × time)),
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus (l1 ++ l2) = some B →
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus l1 = some (B.take l1.length) := by
  intro l2
  induction l2 using List.reverseRecOn with
  | nil =>
    intro B H
    rw [List.append_nil] at H
    have U := fp_claimed_bounds_unzip task_cost task_period task_deadline task_jitter num_cpus l1 B H
    have LEN : B.length = l1.length := by rw [← U, List.length_map]
    rw [← LEN, List.take_length]; exact H
  | append_singleton l2 t IH =>
    intro B H
    rw [← List.append_assoc] at H
    obtain ⟨hp, Hl, _, rfl⟩ := claimed_snoc task_cost task_period task_deadline task_jitter num_cpus (l1 ++ l2) t B H
    have U := fp_claimed_bounds_unzip task_cost task_period task_deadline task_jitter num_cpus _ hp Hl
    have LEN : l1.length ≤ hp.length := by
      rw [← List.length_map (f := Prod.fst), U, List.length_append]; exact Nat.le_add_right _ _
    rw [List.take_append_of_le_length LEN]
    exact IH hp Hl

theorem fp_claimed_bounds_take {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts : List sporadic_task) (hp_bounds : List (sporadic_task × time)) (i : Nat) :
    fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts = some hp_bounds →
    i ≤ hp_bounds.length →
    fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus (ts.take i) = some (hp_bounds.take i) := by
  intro SOME LTi
  have U := fp_claimed_bounds_unzip task_cost task_period task_deadline task_jitter num_cpus ts hp_bounds SOME
  have LEN : hp_bounds.length = ts.length := by rw [← U, List.length_map]
  rw [← List.take_append_drop i ts] at SOME
  have := claimed_append task_cost task_period task_deadline task_jitter num_cpus (ts.take i) (ts.drop i) hp_bounds SOME
  rwa [List.length_take, Nat.min_eq_left (by omega)] at this

theorem fp_claimed_bounds_le_deadline {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts' : List sporadic_task) (rt_bounds : List (sporadic_task × time)) (tsk : sporadic_task) (R : time) :
    fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts' = some rt_bounds →
    (tsk, R) ∈ rt_bounds →
    task_jitter tsk + R ≤ task_deadline tsk := by
  intro SOME IN
  obtain ⟨_, _, LE⟩ := mem_claimed task_cost task_period task_deadline task_jitter num_cpus ts' rt_bounds SOME tsk R IN
  exact LE

theorem fp_claimed_bounds_ge_cost {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts' : List sporadic_task) (rt_bounds : List (sporadic_task × time)) (tsk : sporadic_task) (R : time) :
    fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts' = some rt_bounds →
    (tsk, R) ∈ rt_bounds →
    task_cost tsk ≤ R := by
  intro SOME IN
  obtain ⟨hp, rfl, _⟩ := mem_claimed task_cost task_period task_deadline task_jitter num_cpus ts' rt_bounds SOME tsk R IN
  exact per_task_rta_ge_cost task_cost task_period task_jitter num_cpus tsk hp _

theorem per_task_rta_fold {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (tsk : sporadic_task) (rt_bounds : List (sporadic_task × time)) :
    task_cost tsk +
        div_floor (total_interference_bound_fp task_cost task_period task_jitter tsk rt_bounds
          (per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (max_steps task_cost task_deadline tsk)))
          num_cpus =
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (max_steps task_cost task_deadline tsk + 1) :=
  rfl

/-! ### Higher-priority tasks -/

theorem fp_claimed_bounds_hp_tasks_have_smaller_index {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (higher_priority : FP_policy sporadic_task) (ts : taskset_of sporadic_task)
    (H_task_set_is_sorted : List.IsChain (fun a b => higher_priority a b = true) ts.val)
    (H_task_set_has_unique_priorities : FP_is_antisymmetric_over_task_set higher_priority ts.val)
    (H_priority_transitive : FP_is_transitive higher_priority)
    (hp_bounds : List (sporadic_task × time))
    (H_analysis_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts.val = some hp_bounds)
    (elem : sporadic_task) (hp_idx idx : Nat) :
    hp_idx < ts.val.length →
    idx < ts.val.length →
    (!decide (hp_idx = idx)) = true →
    higher_priority (ts.val.getD hp_idx elem) (ts.val.getD idx elem) = true →
    hp_idx < idx := by
  intro LThp LT NEQ HP
  have LE := sorted_rel_implies_le_idx _ higher_priority ts.val elem H_priority_transitive hp_idx idx ts.nodup
    H_task_set_has_unique_priorities H_task_set_is_sorted HP LThp LT
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NEQ
  omega

/-! ### Convergence of the iteration -/

theorem bertogna_fp_comp_f_monotonic {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts_hp : List sporadic_task) (rt_bounds : List (sporadic_task × time))
    (H_test_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts_hp = some rt_bounds)
    (tsk : sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline (ts_hp ++ [tsk]))
    (x1 x2 : Nat) :
    x1 ≤ x2 →
    per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds x1 ≤
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds x2 := by
  intro LEx
  unfold per_task_rta
  refine fun_mon_iter_mon _ _ x1 x2 LEx (Nat.le_add_right _ _) ?_
  intro a b hab
  apply Nat.add_le_add_left
  apply Nat.div_le_div_right
  have U := fp_claimed_bounds_unzip task_cost task_period task_deadline task_jitter num_cpus ts_hp rt_bounds H_test_succeeds
  unfold total_interference_bound_fp sumSeq
  suffices ∀ L : List (sporadic_task × time), (∀ p, p ∈ L → p ∈ rt_bounds) →
      (L.map (fun (tsk_other, R_other) =>
        interference_bound_generic task_cost task_period task_jitter tsk a (tsk_other, R_other))).sum ≤
      (L.map (fun (tsk_other, R_other) =>
        interference_bound_generic task_cost task_period task_jitter tsk b (tsk_other, R_other))).sum from
    this rt_bounds (fun _ h => h)
  intro L
  induction L with
  | nil => intro _; exact Nat.le_refl _
  | cons p L IH =>
    intro SUB
    simp only [List.map_cons, List.sum_cons]
    apply Nat.add_le_add _ (IH (fun q hq => SUB q (List.mem_cons_of_mem _ hq)))
    obtain ⟨i, R⟩ := p
    have INp : (i, R) ∈ rt_bounds := SUB _ List.mem_cons_self
    have GE_COST := fp_claimed_bounds_ge_cost task_cost task_period task_deadline task_jitter num_cpus ts_hp rt_bounds i R
      H_test_succeeds INp
    have IN' : i ∈ ts_hp := by rw [← U]; exact List.mem_map_of_mem (f := Prod.fst) INp
    have PER : 0 < task_period i := of_decide_eq_true (H_valid_task_parameters i (List.mem_append_left _ IN')).2.1
    unfold interference_bound_generic
    exact min_le_min (W_monotonic task_cost task_period task_jitter i PER R R GE_COST (Nat.le_refl _) a b hab)
      (by omega')

theorem bertogna_fp_comp_f_converges_early {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (rt_bounds : List (sporadic_task × time)) (tsk : sporadic_task) :
    (∃ k, k ≤ max_steps task_cost task_deadline tsk ∧
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k =
        per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (k + 1)) →
    per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (max_steps task_cost task_deadline tsk) =
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (max_steps task_cost task_deadline tsk + 1) := by
  rintro ⟨k, LE, EQ⟩
  exact iter_fix _ _ _ k _ EQ LE

theorem bertogna_fp_comp_f_increases {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts_hp : List sporadic_task) (rt_bounds : List (sporadic_task × time))
    (H_test_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts_hp = some rt_bounds)
    (tsk : sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline (ts_hp ++ [tsk]))
    (H_keeps_diverging : ∀ k, k ≤ max_steps task_cost task_deadline tsk →
      (!decide (per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k =
        per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (k + 1))) = true)
    (k : Nat) :
    k ≤ max_steps task_cost task_deadline tsk →
    per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k <
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (k + 1) := by
  intro LT
  have NE := H_keeps_diverging k LT
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at NE
  exact Nat.lt_of_le_of_ne
    (bertogna_fp_comp_f_monotonic task_cost task_period task_deadline task_jitter num_cpus ts_hp rt_bounds H_test_succeeds tsk
      H_valid_task_parameters k (k + 1) (Nat.le_succ k)) NE

theorem bertogna_fp_comp_rt_grows_too_much {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts_hp : List sporadic_task) (rt_bounds : List (sporadic_task × time))
    (H_test_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts_hp = some rt_bounds)
    (tsk : sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline (ts_hp ++ [tsk]))
    (H_keeps_diverging : ∀ k, k ≤ max_steps task_cost task_deadline tsk →
      (!decide (per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k =
        per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (k + 1))) = true)
    (k : Nat) :
    k ≤ max_steps task_cost task_deadline tsk →
    k + task_cost tsk - 1 < per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k := by
  have COST : 0 < task_cost tsk :=
    of_decide_eq_true (H_valid_task_parameters tsk (List.mem_append_right _ List.mem_cons_self)).1
  induction k with
  | zero =>
    intro _
    show 0 + task_cost tsk - 1 < task_cost tsk
    omega'
  | succ k IH =>
    intro LT
    have IHk := IH (Nat.le_of_succ_le LT)
    have INC := bertogna_fp_comp_f_increases task_cost task_period task_deadline task_jitter num_cpus ts_hp rt_bounds
      H_test_succeeds tsk H_valid_task_parameters H_keeps_diverging k (Nat.le_of_succ_le LT)
    omega'

theorem per_task_rta_converges {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) (num_cpus : Nat)
    (ts_hp : List sporadic_task) (rt_bounds : List (sporadic_task × time))
    (H_test_succeeds : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts_hp = some rt_bounds)
    (tsk : sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline (ts_hp ++ [tsk]))
    (H_no_larger_than_deadline :
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (max_steps task_cost task_deadline tsk) ≤
        task_deadline tsk) :
    per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (max_steps task_cost task_deadline tsk) =
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (max_steps task_cost task_deadline tsk + 1) := by
  by_cases EX : ∃ k, k ≤ max_steps task_cost task_deadline tsk ∧
      per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k =
        per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (k + 1)
  · exact bertogna_fp_comp_f_converges_early task_cost task_period task_deadline task_jitter num_cpus rt_bounds tsk EX
  · exfalso
    have DIFF : ∀ k, k ≤ max_steps task_cost task_deadline tsk →
        (!decide (per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds k =
          per_task_rta task_cost task_period task_jitter num_cpus tsk rt_bounds (k + 1))) = true := by
      intro k hk
      simp only [Bool.not_eq_true', decide_eq_false_iff_not]
      exact fun h => EX ⟨k, hk, h⟩
    have TOO := bertogna_fp_comp_rt_grows_too_much task_cost task_period task_deadline task_jitter num_cpus ts_hp rt_bounds
      H_test_succeeds tsk H_valid_task_parameters DIFF _ (Nat.le_refl _)
    have PARAMS := H_valid_task_parameters tsk (List.mem_append_right _ List.mem_cons_self)
    have COST : 0 < task_cost tsk := of_decide_eq_true PARAMS.1
    have CDL : task_cost tsk ≤ task_deadline tsk := of_decide_eq_true PARAMS.2.2.2.1
    unfold max_steps at TOO H_no_larger_than_deadline
    omega'

/-! ### Main proof -/

/-- LEAN_HELPER: the bounds computed for any prefix of the (sorted) task set are safe. -/
private theorem prefix_bounds_safe {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (num_cpus : Nat)
    (higher_priority : FP_policy sporadic_task) (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_task_set_is_sorted : List.IsChain (fun a b => higher_priority a b = true) ts.val)
    (H_task_set_has_unique_priorities : FP_is_antisymmetric_over_task_set higher_priority ts.val)
    (H_priority_transitive : FP_is_transitive higher_priority)
    (arr_seq : arrival_sequence Job)
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (sched : schedule Job num_cpus) (H_at_least_one_cpu : 0 < num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task job_jitter arr_seq sched higher_priority) :
    ∀ (l suf : List sporadic_task) (B : List (sporadic_task × time)), l ++ suf = ts.val →
      fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus l = some B →
      ∀ tsk R, (tsk, R) ∈ B → is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
    intro suf B _ H tsk R IN
    simp only [fp_claimed_bounds, List.foldl_nil, Option.some.injEq] at H
    subst H; simp at IN
  | append_singleton l t IH =>
    intro suf B PRE H tsk R IN
    obtain ⟨hp, Hl, LE, rfl⟩ := claimed_snoc task_cost task_period task_deadline task_jitter num_cpus l t B H
    have PRE' : l ++ t :: suf = ts.val := by rw [← PRE]; simp
    have IHl := IH (t :: suf) hp PRE' Hl
    rcases List.mem_append.mp IN with INhp | INlast
    · exact IHl tsk R INhp
    simp only [List.mem_singleton, Prod.mk.injEq] at INlast
    obtain ⟨rfl, rfl⟩ := INlast
    have U := fp_claimed_bounds_unzip task_cost task_period task_deadline task_jitter num_cpus l hp Hl
    have INt : tsk ∈ ts := by show tsk ∈ ts.val; rw [← PRE']; simp
    have VALIDl : valid_sporadic_taskset task_cost task_period task_deadline (l ++ [tsk]) := by
      intro x hx
      apply H_valid_task_parameters x
      rw [← PRE']
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ hx
      · rw [List.mem_singleton.mp hx]; simp
    refine bertogna_cirinei_response_time_bound_fp task_cost task_period task_deadline task_jitter job_arrival
      job_cost job_deadline job_task job_jitter H_sporadic_tasks H_valid_job_parameters ts H_valid_task_parameters
      H_constrained_deadlines H_all_jobs_from_taskset num_cpus sched H_jobs_come_from_arrival_sequence
      H_sequential_jobs H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_at_least_one_cpu
      higher_priority H_work_conserving H_respects_FP_policy tsk INt hp IHl ?_
      (fun hp_tsk R_hp IN => fp_claimed_bounds_ge_cost task_cost task_period task_deadline task_jitter num_cpus l hp
        hp_tsk R_hp Hl IN)
      (fun hp_tsk R_hp IN => fp_claimed_bounds_le_deadline task_cost task_period task_deadline task_jitter num_cpus l
        hp hp_tsk R_hp Hl IN) _ ?_ LE
    · intro hp_tsk INhp HP
      unfold higher_priority_task at HP
      simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at HP
      have INl : hp_tsk ∈ l := by
        have INts : hp_tsk ∈ l ++ tsk :: suf := by rw [PRE']; exact INhp
        rcases List.mem_append.mp INts with h | h
        · exact h
        rcases List.mem_cons.mp h with h | h
        · exact absurd h HP.2
        exfalso
        have SORT : List.IsChain (fun a b => higher_priority a b = true) (l ++ tsk :: suf) := by
          rw [PRE']; exact H_task_set_is_sorted
        have PW := chain_pairwise _ (fun y x z h1 h2 => H_priority_transitive y x z h1 h2) _ SORT
        have PWt := (List.pairwise_append.mp PW).2.1
        have HPt : higher_priority tsk hp_tsk = true := List.rel_of_pairwise_cons PWt h
        have INts' : tsk ∈ ts.val := by rw [← PRE']; simp
        exact HP.2 (H_task_set_has_unique_priorities hp_tsk tsk INhp INts' HP.1 HPt)
      rw [← U] at INl
      obtain ⟨⟨x, R_hp⟩, INp, EQ⟩ := List.mem_map.mp INl
      simp only at EQ
      subst EQ
      exact ⟨R_hp, INp⟩
    · rw [per_task_rta_fold]
      exact per_task_rta_converges task_cost task_period task_deadline task_jitter num_cpus l hp Hl tsk VALIDl
        (Nat.le_trans (Nat.le_add_left _ _) LE)

theorem fp_analysis_yields_response_time_bounds {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (num_cpus : Nat)
    (higher_priority : FP_policy sporadic_task) (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_task_set_is_sorted : List.IsChain (fun a b => higher_priority a b = true) ts.val)
    (H_task_set_has_unique_priorities : FP_is_antisymmetric_over_task_set higher_priority ts.val)
    (H_priority_is_total : FP_is_total_over_task_set higher_priority ts.val)
    (H_priority_transitive : FP_is_transitive higher_priority)
    {arr_seq : arrival_sequence Job}
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (sched : schedule Job num_cpus) (H_at_least_one_cpu : 0 < num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task job_jitter arr_seq sched higher_priority) :
    ∀ (tsk : sporadic_task) (R : time),
      optIn (tsk, R) (fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts.val) = true →
      is_response_time_bound_of_task job_arrival job_cost job_task arr_seq sched tsk (task_jitter tsk + R) := by
  intro tsk R MATCH
  cases SOME : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts.val with
  | none => rw [SOME] at MATCH; simp [optIn] at MATCH
  | some hp_bounds =>
    rw [SOME] at MATCH
    simp only [optIn, decide_eq_true_eq] at MATCH
    exact prefix_bounds_safe task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter num_cpus
      higher_priority ts H_valid_task_parameters H_constrained_deadlines H_task_set_is_sorted
      H_task_set_has_unique_priorities H_priority_transitive arr_seq H_all_jobs_from_taskset H_valid_job_parameters
      H_sporadic_tasks sched H_at_least_one_cpu H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute
      H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving H_respects_FP_policy ts.val [] hp_bounds
      (List.append_nil _) SOME tsk R MATCH

theorem taskset_schedulable_by_fp_rta {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (num_cpus : Nat)
    (higher_priority : FP_policy sporadic_task) (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_task_set_is_sorted : List.IsChain (fun a b => higher_priority a b = true) ts.val)
    (H_task_set_has_unique_priorities : FP_is_antisymmetric_over_task_set higher_priority ts.val)
    (H_priority_is_total : FP_is_total_over_task_set higher_priority ts.val)
    (H_priority_transitive : FP_is_transitive higher_priority)
    {arr_seq : arrival_sequence Job}
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (sched : schedule Job num_cpus) (H_at_least_one_cpu : 0 < num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task job_jitter arr_seq sched higher_priority)
    (H_test_succeeds : fp_schedulable task_cost task_period task_deadline task_jitter num_cpus ts.val = true) :
    ∀ tsk, tsk ∈ ts → task_misses_no_deadline job_arrival job_cost job_deadline job_task arr_seq sched tsk := by
  intro tsk INtsk
  unfold fp_schedulable at H_test_succeeds
  cases SOME : fp_claimed_bounds task_cost task_period task_deadline task_jitter num_cpus ts.val with
  | none => rw [SOME] at H_test_succeeds; simp at H_test_succeeds
  | some rt_bounds =>
    have U := fp_claimed_bounds_unzip task_cost task_period task_deadline task_jitter num_cpus ts.val rt_bounds SOME
    have INv : tsk ∈ ts.val := INtsk
    rw [← U] at INv
    obtain ⟨⟨x, R⟩, INp, EQ⟩ := List.mem_map.mp INv
    simp only at EQ
    subst EQ
    have DL := fp_claimed_bounds_le_deadline task_cost task_period task_deadline task_jitter num_cpus ts.val rt_bounds x R
      SOME INp
    have RESP := fp_analysis_yields_response_time_bounds task_cost task_period task_deadline task_jitter job_arrival job_cost
      job_deadline job_task job_jitter num_cpus higher_priority ts H_valid_task_parameters H_constrained_deadlines
      H_task_set_is_sorted H_task_set_has_unique_priorities H_priority_is_total H_priority_transitive
      H_all_jobs_from_taskset H_valid_job_parameters H_sporadic_tasks sched H_at_least_one_cpu
      H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute
      H_sequential_jobs H_work_conserving H_respects_FP_policy x R (by rw [SOME]; simp [optIn, INp])
    intro j ARRj JOBtsk
    have COMP := RESP j ARRj JOBtsk
    have JDL : job_deadline j = task_deadline (job_task j) := (H_valid_job_parameters j ARRj).1.2.2
    unfold job_misses_no_deadline
    apply completion_monotonic job_cost sched j _ _ _ COMP
    rw [JDL, JOBtsk]
    exact Nat.add_le_add_left DL _

theorem jobs_schedulable_by_fp_rta {sporadic_task : Type u} [DecidableEq sporadic_task]
    (task_cost task_period task_deadline task_jitter : sporadic_task → time) {Job : Type v} [DecidableEq Job]
    (job_arrival job_cost job_deadline : Job → time) (job_task : Job → sporadic_task) (job_jitter : Job → time)
    (num_cpus : Nat)
    (higher_priority : FP_policy sporadic_task) (ts : taskset_of sporadic_task)
    (H_valid_task_parameters : valid_sporadic_taskset task_cost task_period task_deadline ts.val)
    (H_constrained_deadlines : ∀ tsk, tsk ∈ ts → task_deadline tsk ≤ task_period tsk)
    (H_task_set_is_sorted : List.IsChain (fun a b => higher_priority a b = true) ts.val)
    (H_task_set_has_unique_priorities : FP_is_antisymmetric_over_task_set higher_priority ts.val)
    (H_priority_is_total : FP_is_total_over_task_set higher_priority ts.val)
    (H_priority_transitive : FP_is_transitive higher_priority)
    {arr_seq : arrival_sequence Job}
    (H_all_jobs_from_taskset : ∀ j, arrives_in arr_seq j → job_task j ∈ ts)
    (H_valid_job_parameters : ∀ j, arrives_in arr_seq j →
      valid_sporadic_job_with_jitter task_cost task_deadline task_jitter job_cost job_deadline job_task job_jitter j)
    (H_sporadic_tasks : sporadic_task_model task_period job_arrival job_task arr_seq)
    (sched : schedule Job num_cpus) (H_at_least_one_cpu : 0 < num_cpus)
    (H_jobs_come_from_arrival_sequence : jobs_come_from_arrival_sequence sched arr_seq)
    (H_jobs_must_arrive_to_execute : jobs_execute_after_jitter job_arrival job_jitter sched)
    (H_completed_jobs_dont_execute : completed_jobs_dont_execute job_cost sched)
    (H_sequential_jobs : sequential_jobs sched)
    (H_work_conserving : work_conserving job_arrival job_cost job_jitter arr_seq sched)
    (H_respects_FP_policy :
      respects_FP_policy job_arrival job_cost job_task job_jitter arr_seq sched higher_priority)
    (H_test_succeeds : fp_schedulable task_cost task_period task_deadline task_jitter num_cpus ts.val = true) :
    ∀ j, arrives_in arr_seq j → job_misses_no_deadline job_arrival job_cost job_deadline sched j = true := by
  intro j ARRj
  exact taskset_schedulable_by_fp_rta task_cost task_period task_deadline task_jitter job_arrival job_cost job_deadline job_task job_jitter
    num_cpus higher_priority ts H_valid_task_parameters H_constrained_deadlines H_task_set_is_sorted
    H_task_set_has_unique_priorities H_priority_is_total H_priority_transitive H_all_jobs_from_taskset
    H_valid_job_parameters H_sporadic_tasks sched H_at_least_one_cpu H_jobs_come_from_arrival_sequence
    H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute H_sequential_jobs H_work_conserving
    H_respects_FP_policy H_test_succeeds (job_task j) (H_all_jobs_from_taskset j ARRj) j ARRj rfl

end Prosa.Classic.Analysis.Global.Jitter.BertognaFpComp.ResponseTimeIterationFP
