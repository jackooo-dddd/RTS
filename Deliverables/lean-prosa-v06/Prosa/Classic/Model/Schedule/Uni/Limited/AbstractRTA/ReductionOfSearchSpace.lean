-- Authoritative source:
-- ProsaBuddy classic Prosa (prosabuddy commit f692cb7479780cf6009493f373a309e13165201c)
-- source: classic/model/schedule/uni/limited/abstract_RTA/reduction_of_search_space.v
-- sha256: see Prosa-Shunqi/classic-prosa/comprehensive-classic/file_order.csv (rank 55)

import Prosa.Classic.Util.All
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule

/-!
Reduction of the search space of the abstract RTA (Rocq module `AbstractRTAReduction`).

Representation notes (as in the accepted v0.6 `analysis/abstract/search_space.v`, which this file predates):
* `ε` is the v0.6 util notation for `1`; a Boolean chain `0 < A < B` in proposition position is
  `(decide (0 < A) && decide (A < B)) = true`; `A_sp <= A <= A_sp + F_sp` likewise.
* Binder lists follow the Rocq contract: `solution_for_A_exists` takes the (unused) section hypotheses
  `H_less_than` and `H_fixpoint`.
-/

set_option linter.unusedVariables false

namespace Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.ReductionOfSearchSpace.AbstractRTAReduction

open Prosa.Classic.Model.Time.Time
open Prosa.Util.Epsilon

universe u

local macro "omega'" : tactic =>
  `(tactic| ((try dsimp only [Prosa.Classic.Model.Time.Time.time,
    Prosa.Classic.Model.Time.Time.instant, Prosa.Classic.Model.Time.Time.duration] at *) <;>
    omega))

def are_equivalent_at_values_less_than {T : Type u} [DecidableEq T] (f1 f2 : Nat → T) (B : Nat) : Prop :=
  ∀ x, x < B → f1 x = f2 x

def are_not_equivalent_at_values_less_than {T : Type u} [DecidableEq T] (f1 f2 : Nat → T) (B : Nat) : Prop :=
  ∃ x, x < B ∧ f1 x ≠ f2 x

def is_in_search_space {Task : Type u} [DecidableEq Task] (tsk : Task) (B : time)
    (interference_bound_function : Task → time → time → time) (A : Nat) : Prop :=
  A = 0 ∨
    (decide (0 < A) && decide (A < B)) = true ∧
      are_not_equivalent_at_values_less_than (interference_bound_function tsk (A - ε))
        (interference_bound_function tsk A) B

/-- LEAN_HELPER: two functions either agree below `B` or have a witness below `B` (as in v0.6). -/
private theorem bounded_equivalent_or_witness (f1 f2 : Nat → Nat) (B : Nat) :
    (∀ x, x < B → f1 x = f2 x) ∨ (∃ x, x < B ∧ f1 x ≠ f2 x) := by
  induction B with
  | zero => left; intro x hx; exact False.elim (Nat.not_lt_zero x hx)
  | succ n ih =>
      rcases ih with hsame | ⟨x, hx, hne⟩
      · by_cases heq : f1 n = f2 n
        · left
          intro x hx
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hx) with hlt | hxeq
          · exact hsame x hlt
          · subst x; exact heq
        · right; exact ⟨n, Nat.lt_succ_self n, heq⟩
      · right; exact ⟨x, Nat.lt_trans hx (Nat.lt_succ_self n), hne⟩

theorem representative_exists {Task : Type u} [DecidableEq Task] (tsk : Task) (B : time)
    (interference_bound_function : Task → time → time → time) (A : time) (H_A_less_than_B : A < B) :
    ∃ A_sp,
      A_sp ≤ A ∧
      are_equivalent_at_values_less_than (interference_bound_function tsk A)
        (interference_bound_function tsk A_sp) B ∧
      is_in_search_space tsk B interference_bound_function A_sp := by
  induction A with
  | zero => exact ⟨0, le_rfl, fun x _ => rfl, Or.inl rfl⟩
  | succ n ih =>
      have hn : n < B := Nat.lt_of_succ_lt H_A_less_than_B
      rcases bounded_equivalent_or_witness (interference_bound_function tsk n)
          (interference_bound_function tsk (n + 1)) B with hsame | hchange
      · obtain ⟨A_sp, hle, heq, hsp⟩ := ih hn
        exact ⟨A_sp, Nat.le_trans hle (Nat.le_succ n), fun x hx => (hsame x hx).symm.trans (heq x hx), hsp⟩
      · refine ⟨n + 1, le_rfl, fun x _ => rfl, Or.inr ⟨?_, ?_⟩⟩
        · simp only [Bool.and_eq_true, decide_eq_true_eq]; exact ⟨Nat.zero_lt_succ n, H_A_less_than_B⟩
        · have h1 : n + 1 - ε = n := by simp
          rw [h1]; exact hchange

theorem solution_for_A_exists {Task : Type u} [DecidableEq Task] (tsk : Task) (B : time)
    (interference_bound_function : Task → time → time → time) (A_sp F_sp : time) (H_less_than : A_sp + F_sp < B)
    (H_fixpoint : A_sp + F_sp = interference_bound_function tsk A_sp (A_sp + F_sp)) (A : time)
    (H_bounds_for_A : (decide (A_sp ≤ A) && decide (A ≤ A_sp + F_sp)) = true)
    (H_equivalent : are_equivalent_at_values_less_than (interference_bound_function tsk A)
      (interference_bound_function tsk A_sp) B) :
    ∃ F, A_sp + F_sp = A + F ∧ F ≤ F_sp ∧ A + F = interference_bound_function tsk A (A + F) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at H_bounds_for_A
  obtain ⟨NEQ1, NEQ2⟩ := H_bounds_for_A
  refine ⟨A_sp + F_sp - A, by omega', by omega', ?_⟩
  have hX : A + (A_sp + F_sp - A) = A_sp + F_sp := by omega'
  rw [hX, H_equivalent _ H_less_than]
  exact H_fixpoint

end Prosa.Classic.Model.Schedule.Uni.Limited.AbstractRTA.ReductionOfSearchSpace.AbstractRTAReduction
