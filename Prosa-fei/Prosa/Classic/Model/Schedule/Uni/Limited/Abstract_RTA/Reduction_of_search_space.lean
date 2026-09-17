-- Translated from: ../rt-proofs/classic/model/schedule/uni/limited/abstract_RTA/reduction_of_search_space.v
import Prosa.Classic.Model.Arrival.Basic.Job
import Prosa.Classic.Model.Schedule.Uni.Schedule
import Prosa.Util.Epsilon
import Mathlib.Tactic

namespace Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Reduction_of_search_space

open Prosa.Classic.Model.Time
open Prosa.Util.Epsilon

namespace AbstractRTAReduction

section SearchSpace

variable {Task : Type _} [DecidableEq Task]

section EquivalentFunctions

variable {T : Type _} [DecidableEq T]

variable (f1 f2 : Nat → T)

variable (B : Nat)

def are_equivalent_at_values_less_than :=
  ∀ x, x < B → f1 x = f2 x

def are_not_equivalent_at_values_less_than :=
  ∃ x, x < B ∧ f1 x ≠ f2 x

end EquivalentFunctions

variable (tsk : Task)

variable (B : Time)

variable (interference_bound_function : Task → Time → Time → Time)

def is_in_search_space (A : Time) :=
  A = 0 ∨
  0 < A ∧ A < B ∧ are_not_equivalent_at_values_less_than
    (interference_bound_function tsk (A - ε)) (interference_bound_function tsk A) B

section ExistenceOfRepresentative

variable (A : Time)
variable (H_A_less_than_B : A < B)
include H_A_less_than_B

theorem representative_exists :
  ∃ A_sp,
    A_sp ≤ A ∧
    are_equivalent_at_values_less_than (interference_bound_function tsk A)
                                       (interference_bound_function tsk A_sp) B ∧
    is_in_search_space tsk B interference_bound_function A_sp := by
  induction A with
  | zero =>
    exact ⟨0, le_refl 0, fun _ _ => rfl, Or.inl rfl⟩
  | succ n IH =>
    -- Decide: do IBF tsk n and IBF tsk (n+1) agree on all values < B?
    by_cases hAgree : ∀ x, x < B → interference_bound_function tsk n x = interference_bound_function tsk (n + 1) x
    · -- They agree: reuse IH
      have hn_lt_B : n < B := by simp only [Time] at *; omega
      obtain ⟨A_sp, hle, hequiv, hsp⟩ := IH hn_lt_B
      exact ⟨A_sp, by simp only [Time] at *; omega, fun x hx => by rw [← hAgree x hx]; exact hequiv x hx, hsp⟩
    · -- They differ: n+1 is in the search space
      push_neg at hAgree
      obtain ⟨x, hxB, hxneq⟩ := hAgree
      refine ⟨n + 1, le_refl _, fun _ _ => rfl, Or.inr ⟨by simp only [Time] at *; omega, by simp only [Time] at *; omega, ?_⟩⟩
      exact ⟨x, hxB, by simp [ε]; exact fun h => hxneq h⟩

end ExistenceOfRepresentative

section FixpointSolutionForAnotherA

variable (A_sp F_sp : Time)
variable (H_less_than : A_sp + F_sp < B)
variable (H_fixpoint : A_sp + F_sp = interference_bound_function tsk A_sp (A_sp + F_sp))

variable (A : Time)
variable (H_bounds_for_A : A_sp ≤ A ∧ A ≤ A_sp + F_sp)
variable (H_equivalent :
  are_equivalent_at_values_less_than
    (interference_bound_function tsk A)
    (interference_bound_function tsk A_sp) B)
include H_less_than H_fixpoint H_bounds_for_A H_equivalent

theorem solution_for_A_exists :
  ∃ F,
    A_sp + F_sp = A + F ∧
    F ≤ F_sp ∧
    A + F = interference_bound_function tsk A (A + F) := by
  obtain ⟨hle1, hle2⟩ := H_bounds_for_A
  refine ⟨A_sp + F_sp - A, ?_, ?_, ?_⟩
  · simp only [Time] at *; omega
  · simp only [Time] at *; omega
  · have hAF : A + (A_sp + F_sp - A) = A_sp + F_sp := by simp only [Time] at *; omega
    rw [hAF]
    rw [H_equivalent (A_sp + F_sp) H_less_than]
    exact H_fixpoint

end FixpointSolutionForAnotherA

end SearchSpace

end AbstractRTAReduction

end Prosa.Classic.Model.Schedule.Uni.Limited.Abstract_RTA.Reduction_of_search_space
