-- Translated from: ../rt-proofs/analysis/abstract/search_space.v
import Prosa.Util.Epsilon
import Prosa.Util.Tactics
import Prosa.Model.Task.Concept

namespace Prosa.Analysis.Abstract.Search_space

open Prosa.Util.Epsilon
open Prosa.Model.Task.Concept
open Prosa.Behavior.Time

section AbstractRTAReduction

  variable {Task : TaskType}

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

  variable (B : duration)

  variable (interference_bound_function : Task → duration → duration → duration)

  def is_in_search_space (A : Nat) :=
    A = 0 ∨
    (0 < A ∧ A < B) ∧ are_not_equivalent_at_values_less_than
                  (interference_bound_function tsk (A - ε)) (interference_bound_function tsk A) B

  section ExistenceOfRepresentative

    variable (A : duration)

    theorem representative_exists (H_A_less_than_B : A < B) :
      ∃ A_sp,
        A_sp ≤ A ∧
        are_equivalent_at_values_less_than (interference_bound_function tsk A)
                                           (interference_bound_function tsk A_sp) B ∧
        is_in_search_space tsk B interference_bound_function A_sp := by
      induction A with
      | zero =>
        exact ⟨0, le_refl 0, fun _ _ => rfl, Or.inl rfl⟩
      | succ n IH =>
        -- Decide: are ibf tsk n and ibf tsk (n+1) equivalent at all values < B?
        by_cases h_eq : ∀ x, x < B → interference_bound_function tsk n x = interference_bound_function tsk (n + 1) x
        · -- Case 1: they are equivalent, use the IH representative
          have hn_lt_B : n < B := Nat.lt_of_succ_lt H_A_less_than_B
          obtain ⟨A_sp, hle, hequiv, hsp⟩ := IH hn_lt_B
          exact ⟨A_sp, Nat.le_succ_of_le hle,
            fun x hx => by rw [← h_eq x hx, hequiv x hx], hsp⟩
        · -- Case 2: they differ, use A_sp = n + 1
          push_neg at h_eq
          obtain ⟨x, hxB, hne⟩ := h_eq
          refine ⟨n + 1, le_refl _, fun _ _ => rfl, Or.inr ⟨⟨Nat.succ_pos n, H_A_less_than_B⟩, ?_⟩⟩
          refine ⟨x, hxB, ?_⟩
          simp [ε]
          exact hne

  end ExistenceOfRepresentative

  section FixpointSolutionForAnotherA

    variable (A_sp F_sp : duration)
    variable (A : duration)

    theorem solution_for_A_exists
      (H_less_than : A_sp + F_sp < B)
      (H_fixpoint : A_sp + F_sp = interference_bound_function tsk A_sp (A_sp + F_sp))
      (H_bounds_for_A : A_sp ≤ A ∧ A ≤ A_sp + F_sp)
      (H_equivalent :
        are_equivalent_at_values_less_than
          (interference_bound_function tsk A)
          (interference_bound_function tsk A_sp) B) :
      ∃ F,
        A_sp + F_sp = A + F ∧
        F ≤ F_sp ∧
        A + F = interference_bound_function tsk A (A + F) := by
      obtain ⟨hle1, hle2⟩ := H_bounds_for_A
      refine ⟨A_sp + F_sp - A, ?_, ?_, ?_⟩
      · exact (Nat.add_sub_cancel' hle2).symm
      · -- A_sp + F_sp - A ≤ F_sp, given A_sp ≤ A
        calc A_sp + F_sp - A ≤ A_sp + F_sp - A_sp := Nat.sub_le_sub_left hle1 _
          _ = F_sp := Nat.add_sub_cancel_left _ _
      · have h1 : A + (A_sp + F_sp - A) = A_sp + F_sp :=
          Nat.add_sub_cancel' hle2
        rw [h1]
        rw [H_equivalent (A_sp + F_sp) H_less_than]
        exact H_fixpoint

  end FixpointSolutionForAnotherA

end AbstractRTAReduction

end Prosa.Analysis.Abstract.Search_space
