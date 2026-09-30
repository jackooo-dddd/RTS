import Prosa.Model.Processor.Multiprocessor
import Mathlib.Algebra.BigOperators.Fin
import Validation.fixtures.translation_order.SuspensionComputationInterface

/-!
Export root for `model/processor/multiprocessor.v`: the processor type, the multiprocessor state, the three
per-processor observations, the section-local multiprocessor instance (helper) and the lemma, together with the
accepted suspension/Service export root, and a validation-only list form of the finite sum over `Fin n`.
-/

open scoped BigOperators

namespace Prosa.Validation.MultiprocessorInterface

/-- Validation-only list form of the finite sum over `Fin n` (exported with its proof body and all proof
dependencies): each ordinal is visited through its value in the ascending range. -/

theorem foldr_add_snoc (l : List Nat) (x : Nat) :
    List.foldr Nat.add 0 (l ++ [x]) = List.foldr Nat.add 0 l + x := by
  induction l with
  | nil => show x + 0 = 0 + x; omega
  | cons a l ih =>
    rw [List.cons_append, List.foldr_cons, List.foldr_cons, ih]
    show a + (List.foldr Nat.add 0 l + x) = a + List.foldr Nat.add 0 l + x
    omega

theorem range_sum_foldr (g : Nat → Nat) : ∀ m : Nat,
    (∑ i ∈ Finset.range m, g i) = List.foldr Nat.add 0 ((List.range' 0 m).map g)
  | 0 => by simp
  | m + 1 => by
    rw [Finset.sum_range_succ, range_sum_foldr g m, List.range'_concat, List.map_append,
      List.map_cons, List.map_nil, foldr_add_snoc]
    simp

theorem production_fin_sum (n : Nat) (f : Fin n → Nat) :
    (∑ i : Fin n, f i) =
      List.foldr Nat.add 0 ((List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else 0)) := by
  have hg : ∀ i : Fin n, f i = (fun k => if h : k < n then f ⟨k, h⟩ else 0) (i : Nat) := by
    intro i; simp [i.isLt]
  rw [Finset.sum_congr rfl (fun i _ => hg i), Fin.sum_univ_eq_sum_range (fun k => if h : k < n then f ⟨k, h⟩ else 0) n]
  exact range_sum_foldr _ n

end Prosa.Validation.MultiprocessorInterface
