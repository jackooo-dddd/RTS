-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/policy_tdma.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 38)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Time
import Prosa.Classic.Model.Arrival.Basic.Task
import Prosa.Classic.Model.Arrival.Basic.Job

/-!
The TDMA policy (Rocq module `PolicyTDMA`).

Representation notes:
* `TDMA_slot Task := Task -> duration` and `TDMA_slot_order Task := rel Task` (a Boolean relation) are
  reducible type definitions (`abbrev`) with `Task` explicit, as in the source section `TDMA`.
* `{set Task}` is the v0.6 sequence-set `Prosa.Util.Seqset.set Task`; `ts` used as a sequence is `ts.val`.
* MathComp's `transitive slot_order` is `∀ y x z, slot_order x y = true → slot_order y z = true →
  slot_order x z = true` (MathComp's binder order, as in classic `Fixedpoint`); `total_over_list` and
  `antisymmetric_over_list` are the classic `Prosa.Classic.Util.List` definitions.
* `\sum_(x <- s) F x` is `sumSeq s F` and `\sum_(x <- s | P x) F x` is `sumFiltered s P F`; `a != b` in a
  Boolean expression is `!decide (a = b)`; `%%` is `%`; `x > 0` returning `bool` is `decide (0 < x)`.
* Boolean tests in proposition position are `= true`; ssrnat comparisons in proposition position are the
  Nat order.
* Binder lists follow the Rocq contract: each declaration takes exactly the section variables and
  hypotheses Rocq abstracts (e.g. `relation_offset` does not take the totality hypothesis).
-/

namespace Prosa.Classic.Model.PolicyTdma.PolicyTDMA

open Prosa.Classic.Model.Time.Time
open Prosa.Util.Seqset
open Prosa.Util.Sum (sumSeq sumFiltered)
open Prosa.Classic.Util.List (total_over_list antisymmetric_over_list)

universe u

abbrev TDMA_slot (Task : Type u) [DecidableEq Task] := Task → duration

abbrev TDMA_slot_order (Task : Type u) [DecidableEq Task] := Task → Task → Bool

def slot_order_is_transitive {Task : Type u} [DecidableEq Task] (slot_order : TDMA_slot_order Task) : Prop :=
  ∀ y x z, slot_order x y = true → slot_order y z = true → slot_order x z = true

def slot_order_is_total_over_task_set {Task : Type u} [DecidableEq Task] (ts : set Task)
    (slot_order : TDMA_slot_order Task) : Prop :=
  total_over_list slot_order ts.val

def slot_order_is_antisymmetric_over_task_set {Task : Type u} [DecidableEq Task] (ts : set Task)
    (slot_order : TDMA_slot_order Task) : Prop :=
  antisymmetric_over_list slot_order ts.val

def is_valid_time_slot {Task : Type u} [DecidableEq Task] (task : Task) (task_time_slot : TDMA_slot Task) :
    Bool :=
  decide (0 < task_time_slot task)

def TDMA_cycle {Task : Type u} [DecidableEq Task] (ts : set Task) (task_time_slot : TDMA_slot Task) : Nat :=
  sumSeq ts.val task_time_slot

def Task_slot_offset {Task : Type u} [DecidableEq Task] (ts : set Task) (slot_order : TDMA_slot_order Task)
    (task : Task) (task_time_slot : TDMA_slot Task) : Nat :=
  sumFiltered ts.val (fun prev_task => slot_order prev_task task && !decide (prev_task = task)) task_time_slot

def Task_in_time_slot {Task : Type u} [DecidableEq Task] (ts : set Task) (slot_order : TDMA_slot_order Task)
    (task : Task) (task_time_slot : TDMA_slot Task) (t : time) : Bool :=
  decide ((t + TDMA_cycle ts task_time_slot - Task_slot_offset ts slot_order task task_time_slot %
      TDMA_cycle ts task_time_slot) % TDMA_cycle ts task_time_slot < task_time_slot task)

/-! Proof-local sum facts (as in the accepted v0.6 `analysis/facts/tdma.v`). -/

private theorem sum_map_eq_foldr {α : Type u} (f : α → Nat) :
    ∀ xs : List α, (xs.map f).sum = xs.foldr (fun x n => f x + n) 0
  | [] => rfl
  | a :: xs => by simp [sum_map_eq_foldr f xs]

private theorem foldr_sum_filter_mono {α : Type u} (f : α → Nat) (P Q : α → Bool) :
    ∀ xs : List α, (∀ x, x ∈ xs → P x = true → Q x = true) →
      (xs.filter P).foldr (fun x n => f x + n) 0 ≤
        (xs.filter Q).foldr (fun x n => f x + n) 0
  | [] => fun _ => Nat.le_refl _
  | a :: xs => fun hPQ => by
      have ih := foldr_sum_filter_mono f P Q xs
        (fun x hx hP => hPQ x (List.mem_cons_of_mem a hx) hP)
      by_cases hP : P a = true
      · have hQ := hPQ a List.mem_cons_self hP
        simp only [List.filter_cons, hP, hQ, if_true, List.foldr_cons]; omega
      · by_cases hQ : Q a = true
        · simp only [List.filter_cons, hP, hQ, if_true, List.foldr_cons]; simp; omega
        · simp only [List.filter_cons, hP, hQ]; simp; omega

private theorem foldr_sum_filter_add_le {α : Type u} [DecidableEq α] (f : α → Nat)
    (P Q : α → Bool) (t : α) :
    ∀ xs : List α, t ∈ xs → P t = false → Q t = true →
      (∀ x, x ∈ xs → P x = true → Q x = true) →
      (xs.filter P).foldr (fun x n => f x + n) 0 + f t ≤
        (xs.filter Q).foldr (fun x n => f x + n) 0
  | [] => fun h => absurd h List.not_mem_nil
  | a :: xs => fun hmem hPt hQt hPQ => by
      have hPQ' : ∀ x, x ∈ xs → P x = true → Q x = true :=
        fun x hx hP => hPQ x (List.mem_cons_of_mem a hx) hP
      by_cases hat : a = t
      · subst hat
        have hmono := foldr_sum_filter_mono f P Q xs hPQ'
        simp only [List.filter_cons, hPt, hQt, if_true, List.foldr_cons]; simp; omega
      · have ht : t ∈ xs := by
          rcases List.mem_cons.mp hmem with h | h
          · exact absurd h.symm hat
          · exact h
        have ih := foldr_sum_filter_add_le f P Q t xs ht hPt hQt hPQ'
        by_cases hP : P a = true
        · have hQ := hPQ a List.mem_cons_self hP
          simp only [List.filter_cons, hP, hQ, if_true, List.foldr_cons]; omega
        · by_cases hQ : Q a = true
          · simp only [List.filter_cons, hP, hQ, if_true, List.foldr_cons]; simp; omega
          · simp only [List.filter_cons, hP, hQ]; simp; omega

private theorem offset_add_slot_le {Task : Type u} [DecidableEq Task] (ts : set Task)
    (slot_order : TDMA_slot_order Task) (task : Task) (task_time_slot : TDMA_slot Task) (h : task ∈ ts) :
    Task_slot_offset ts slot_order task task_time_slot + task_time_slot task ≤ TDMA_cycle ts task_time_slot := by
  have hle := foldr_sum_filter_add_le (fun x => task_time_slot x)
    (fun p => slot_order p task && !decide (p = task)) (fun _ => true) task ts.val (show task ∈ ts.val from h)
    (by simp) rfl (fun _ _ _ => rfl)
  simp only [Task_slot_offset, TDMA_cycle, sumFiltered, sumSeq, sum_map_eq_foldr, List.filter_true] at hle ⊢
  exact hle

theorem TDMA_cycle_ge_each_time_slot {Task : Type u} [DecidableEq Task] (ts : set Task) (task : Task)
    (H_task_in_ts : task ∈ ts) (task_time_slot : TDMA_slot Task) :
    task_time_slot task ≤ TDMA_cycle ts task_time_slot := by
  unfold TDMA_cycle sumSeq
  exact List.le_sum_of_mem (List.mem_map_of_mem (show task ∈ ts.val from H_task_in_ts))

theorem TDMA_cycle_positive {Task : Type u} [DecidableEq Task] (ts : set Task) (task : Task)
    (H_task_in_ts : task ∈ ts) (task_time_slot : TDMA_slot Task)
    (time_slot_positive : is_valid_time_slot task task_time_slot = true) :
    0 < TDMA_cycle ts task_time_slot := by
  simp only [is_valid_time_slot, decide_eq_true_eq] at time_slot_positive
  exact Nat.lt_of_lt_of_le time_slot_positive (TDMA_cycle_ge_each_time_slot ts task H_task_in_ts task_time_slot)

theorem Offset_lt_cycle {Task : Type u} [DecidableEq Task] (ts : set Task) (slot_order : TDMA_slot_order Task)
    (task : Task) (H_task_in_ts : task ∈ ts) (task_time_slot : TDMA_slot Task)
    (time_slot_positive : is_valid_time_slot task task_time_slot = true) :
    Task_slot_offset ts slot_order task task_time_slot < TDMA_cycle ts task_time_slot := by
  have hle := offset_add_slot_le ts slot_order task task_time_slot H_task_in_ts
  simp only [is_valid_time_slot, decide_eq_true_eq] at time_slot_positive
  exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right time_slot_positive) hle

theorem Offset_add_slot_leq_cycle {Task : Type u} [DecidableEq Task] (ts : set Task)
    (slot_order : TDMA_slot_order Task) (task : Task) (H_task_in_ts : task ∈ ts)
    (task_time_slot : TDMA_slot Task) :
    Task_slot_offset ts slot_order task task_time_slot + task_time_slot task ≤ TDMA_cycle ts task_time_slot :=
  offset_add_slot_le ts slot_order task task_time_slot H_task_in_ts

theorem relation_offset {Task : Type u} [DecidableEq Task] (ts : set Task) (slot_order : TDMA_slot_order Task)
    (task_time_slot : TDMA_slot Task)
    (slot_order_antisymmetric : slot_order_is_antisymmetric_over_task_set ts slot_order)
    (slot_order_transitive : slot_order_is_transitive slot_order) :
    ∀ tsk1 tsk2 : Task, tsk1 ∈ ts → tsk2 ∈ ts →
      slot_order tsk1 tsk2 = true → (!decide (tsk1 = tsk2)) = true →
      Task_slot_offset ts slot_order tsk1 task_time_slot + task_time_slot tsk1 ≤
        Task_slot_offset ts slot_order tsk2 task_time_slot := by
  intro tsk1 tsk2 h1 h2 horder hne
  have hne' : tsk1 ≠ tsk2 := by simpa using hne
  simp only [Task_slot_offset, sumFiltered, sum_map_eq_foldr]
  refine foldr_sum_filter_add_le (fun x => task_time_slot x)
    (fun p => slot_order p tsk1 && !decide (p = tsk1))
    (fun p => slot_order p tsk2 && !decide (p = tsk2)) tsk1 ts.val (show tsk1 ∈ ts.val from h1) (by simp)
    (by simp [horder, hne']) ?_
  intro x hx hP
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hP ⊢
  refine ⟨slot_order_transitive tsk1 x tsk2 hP.1 horder, ?_⟩
  intro hx2
  subst hx2
  exact hne' (slot_order_antisymmetric tsk1 x h1 hx horder hP.1)

/-- LEAN_HELPER: inside one cycle, time `t` is in a slot only between its offset and its end (as in the
accepted v0.6 `analysis/facts/tdma.v`). -/
private theorem in_slot_bounds (c O s t : Nat) (hO : O < c) (hOs : O + s ≤ c)
    (h : (t + c - O % c) % c < s) : O ≤ t % c ∧ t % c < O + s := by
  have hc : 0 < c := by omega
  rw [Nat.mod_eq_of_lt hO] at h
  have hr : t % c < c := Nat.mod_lt t hc
  have hdecomp := Nat.mod_add_div t c
  have key : (t + c - O) % c = (t % c + c - O) % c := by
    have hsplit : t + c - O = (t % c + c - O) + c * (t / c) := by omega
    rw [hsplit, Nat.add_mul_mod_self_left]
  rw [key] at h
  by_cases hle : O ≤ t % c
  · have hshift : t % c + c - O = (t % c - O) + c := by omega
    rw [hshift, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)] at h
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at h
    omega

theorem task_in_time_slot_uniq {Task : Type u} [DecidableEq Task] (ts : set Task)
    (slot_order : TDMA_slot_order Task) (task_time_slot : TDMA_slot Task)
    (slot_order_total : slot_order_is_total_over_task_set ts slot_order)
    (slot_order_antisymmetric : slot_order_is_antisymmetric_over_task_set ts slot_order)
    (slot_order_transitive : slot_order_is_transitive slot_order) :
    ∀ (tsk1 tsk2 : Task) (t : time),
      tsk1 ∈ ts → 0 < task_time_slot tsk1 →
      tsk2 ∈ ts → 0 < task_time_slot tsk2 →
      Task_in_time_slot ts slot_order tsk1 task_time_slot t = true →
      Task_in_time_slot ts slot_order tsk2 task_time_slot t = true → tsk1 = tsk2 := by
  intro tsk1 tsk2 t h1 p1 h2 p2 hs1 hs2
  have hO1 := Offset_lt_cycle ts slot_order tsk1 h1 task_time_slot (by simpa [is_valid_time_slot] using p1)
  have hO2 := Offset_lt_cycle ts slot_order tsk2 h2 task_time_slot (by simpa [is_valid_time_slot] using p2)
  have hS1 := Offset_add_slot_leq_cycle ts slot_order tsk1 h1 task_time_slot
  have hS2 := Offset_add_slot_leq_cycle ts slot_order tsk2 h2 task_time_slot
  unfold Task_in_time_slot at hs1 hs2
  have b1 := in_slot_bounds _ _ _ _ hO1 hS1 (of_decide_eq_true hs1)
  have b2 := in_slot_bounds _ _ _ _ hO2 hS2 (of_decide_eq_true hs2)
  by_cases heq : tsk1 = tsk2
  · exact heq
  · exfalso
    rcases slot_order_total tsk1 tsk2 h1 h2 with ho | ho
    · have := relation_offset ts slot_order task_time_slot slot_order_antisymmetric slot_order_transitive
        tsk1 tsk2 h1 h2 ho (by simpa using heq)
      dsimp only [duration, time] at *
      omega
    · have := relation_offset ts slot_order task_time_slot slot_order_antisymmetric slot_order_transitive
        tsk2 tsk1 h2 h1 ho (by simpa using Ne.symm heq)
      dsimp only [duration, time] at *
      omega

end Prosa.Classic.Model.PolicyTdma.PolicyTDMA
