-- Authoritative source:
-- Prosa v0.6
-- commit: 414e66760333eaa4ef78c685bcf53291c527a548
-- source: analysis/abstract/search_space.v

import Mathlib.Tactic
import Prosa.Model.Task.Concept
import Prosa.Util.Epsilon
import Prosa.Util.Tactics

namespace Prosa.Analysis.Abstract.SearchSpace

open Prosa.Behavior.Time
open Prosa.Model.Task.Concept
open Prosa.Util.Epsilon

universe u

/-- Two functions agree at every argument strictly below `B`. -/
def are_equivalent_at_values_less_than {T : Type u} [DecidableEq T]
    (f1 f2 : Nat → T) (B : Nat) : Prop :=
  ∀ x, x < B → f1 x = f2 x

/-- A bounded witness on which two functions disagree. -/
def are_not_equivalent_at_values_less_than {T : Type u} [DecidableEq T]
    (f1 f2 : Nat → T) (B : Nat) : Prop :=
  ∃ x, x < B ∧ f1 x ≠ f2 x

/-- Zero and the bounded change points of an interference-bound function. -/
def is_in_search_space (B : duration)
    (interference_bound_function : duration → duration → duration)
    (A : duration) : Prop :=
  A = 0 ∨
    0 < A ∧ A < B ∧
      are_not_equivalent_at_values_less_than
        (interference_bound_function (A - ε))
        (interference_bound_function A) B

private theorem bounded_equivalent_or_witness (f1 f2 : Nat → Nat) (B : Nat) :
    (∀ x, x < B → f1 x = f2 x) ∨
      (∃ x, x < B ∧ f1 x ≠ f2 x) := by
  induction B with
  | zero =>
      left
      intro x hx
      exact False.elim (Nat.not_lt_zero x hx)
  | succ n ih =>
      rcases ih with hsame | ⟨x, hx, hne⟩
      · match Nat.decEq (f1 n) (f2 n) with
        | isTrue heq =>
          left
          intro x hx
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hx) with hlt | hxeq
          · exact hsame x hlt
          · subst x
            exact heq
        | isFalse hne =>
          right
          exact ⟨n, Nat.lt_succ_self n, hne⟩
      · right
        exact ⟨x, Nat.lt_trans hx (Nat.lt_succ_self n), hne⟩

/-- Every bounded offset has a no-larger search-space representative with
    the same bounded interference. -/
theorem representative_exists (B : duration)
    (interference_bound_function : duration → duration → duration)
    (A : duration) (H_A_less_than_B : A < B) :
    ∃ A_sp,
      A_sp ≤ A ∧
      are_equivalent_at_values_less_than
        (interference_bound_function A)
        (interference_bound_function A_sp) B ∧
      is_in_search_space B interference_bound_function A_sp := by
  induction A with
  | zero =>
      refine ⟨0, le_rfl, ?_, Or.inl rfl⟩
      intro x hx
      rfl
  | succ n ih =>
      have hn : n < B := Nat.lt_of_succ_lt H_A_less_than_B
      rcases bounded_equivalent_or_witness
          (interference_bound_function n)
          (interference_bound_function (n + 1)) B with hsame | hchange
      · obtain ⟨A_sp, hle, heq, hsp⟩ := ih hn
        refine ⟨A_sp, Nat.le_trans hle (Nat.le_succ n), ?_, hsp⟩
        intro x hx
        exact (hsame x hx).symm.trans (heq x hx)
      · have hchange' :
            are_not_equivalent_at_values_less_than
              (interference_bound_function n)
              (interference_bound_function (n + 1)) B := hchange
        refine ⟨n + 1, le_rfl, ?_, Or.inr ?_⟩
        · intro x hx
          rfl
        · refine ⟨Nat.zero_lt_succ n, H_A_less_than_B, ?_⟩
          simpa using hchange'

/-- A fixpoint at a representative offset gives a no-larger response term
    for any equivalent offset in the same interval. -/
theorem solution_for_A_exists (B : duration)
    (interference_bound_function : duration → duration → duration)
    (A_sp F_sp : duration)
    (H_less_than : A_sp + F_sp < B)
    (H_fixpoint :
      interference_bound_function A_sp (A_sp + F_sp) ≤ A_sp + F_sp)
    (A : duration)
    (H_bounds_for_A : A_sp ≤ A ∧ A ≤ A_sp + F_sp)
    (H_equivalent :
      are_equivalent_at_values_less_than
        (interference_bound_function A)
        (interference_bound_function A_sp) B) :
    ∃ F,
      A_sp + F_sp = A + F ∧
      F ≤ F_sp ∧
      interference_bound_function A (A + F) ≤ A + F := by
  obtain ⟨hlow, hhigh⟩ := H_bounds_for_A
  have hsum : A + (A_sp + F_sp - A) = A_sp + F_sp :=
    Nat.add_sub_of_le hhigh
  refine ⟨A_sp + F_sp - A, hsum.symm, ?_, ?_⟩
  · apply Nat.sub_le_iff_le_add.mpr
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (Nat.add_le_add_right hlow F_sp)
  ·
    rw [hsum, H_equivalent (A_sp + F_sp) H_less_than]
    exact H_fixpoint

/-- Pointwise equal interference-bound functions have the same search-space
    membership at bounded offsets. -/
theorem search_space_switch_IBF (B : duration)
    (IBF1 IBF2 : duration → duration → duration)
    (EQU : ∀ A Δ, A < B → IBF1 A Δ = IBF2 A Δ)
    (A : duration)
    (hspace : is_in_search_space B IBF1 A) :
    is_in_search_space B IBF2 A := by
  rcases hspace with hzero | ⟨hpositive, hAB, x, hx, hneq⟩
  · exact Or.inl hzero
  · right
    refine ⟨hpositive, hAB, x, hx, ?_⟩
    have hprev : A - ε < B := Nat.lt_of_le_of_lt (Nat.sub_le A ε) hAB
    intro heq
    apply hneq
    rw [EQU (A - ε) x hprev, EQU A x hAB]
    exact heq

end Prosa.Analysis.Abstract.SearchSpace
