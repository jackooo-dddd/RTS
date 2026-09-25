import Prosa.Analysis.Abstract.SearchSpace

open Prosa.Behavior.Time
open Prosa.Analysis.Abstract.SearchSpace

universe u

#check @are_equivalent_at_values_less_than
#check @are_not_equivalent_at_values_less_than
#check @is_in_search_space
#check @representative_exists
#check @solution_for_A_exists
#check @search_space_switch_IBF

example {T : Type u} [DecidableEq T] (f1 f2 : Nat → T) (B : Nat) :
    are_equivalent_at_values_less_than f1 f2 B ↔
      ∀ x, x < B → f1 x = f2 x := Iff.rfl

example {T : Type u} [DecidableEq T] (f1 f2 : Nat → T) (B : Nat) :
    are_not_equivalent_at_values_less_than f1 f2 B ↔
      ∃ x, x < B ∧ f1 x ≠ f2 x := Iff.rfl

example (B : duration) (ibf : duration → duration → duration) (A : duration) :
    is_in_search_space B ibf A ↔
      (A = 0 ∨ 0 < A ∧ A < B ∧
        are_not_equivalent_at_values_less_than
          (ibf (A - 1)) (ibf A) B) := Iff.rfl

example (B : duration) (ibf : duration → duration → duration)
    (A : duration) (hA : A < B) :
    ∃ A_sp,
      A_sp ≤ A ∧
      are_equivalent_at_values_less_than (ibf A) (ibf A_sp) B ∧
      is_in_search_space B ibf A_sp :=
  representative_exists B ibf A hA

example (B : duration) (ibf : duration → duration → duration)
    (A_sp F_sp : duration)
    (hless : A_sp + F_sp < B)
    (hfix : ibf A_sp (A_sp + F_sp) ≤ A_sp + F_sp)
    (A : duration) (hbounds : A_sp ≤ A ∧ A ≤ A_sp + F_sp)
    (heq : are_equivalent_at_values_less_than (ibf A) (ibf A_sp) B) :
    ∃ F,
      A_sp + F_sp = A + F ∧
      F ≤ F_sp ∧
      ibf A (A + F) ≤ A + F :=
  solution_for_A_exists B ibf A_sp F_sp hless hfix A hbounds heq

example (B : duration) (ibf1 ibf2 : duration → duration → duration)
    (heq : ∀ A Δ, A < B → ibf1 A Δ = ibf2 A Δ)
    (A : duration) (hspace : is_in_search_space B ibf1 A) :
    is_in_search_space B ibf2 A :=
  search_space_switch_IBF B ibf1 ibf2 heq A hspace

#print axioms representative_exists
#print axioms solution_for_A_exists
#print axioms search_space_switch_IBF
