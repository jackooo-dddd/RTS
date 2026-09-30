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
dependencies): each ordinal is visited through its value in the ascending range.  The proof goes through
`List.finRange` (the carrier list of `Fin.fintype`) by element-wise list extensionality; it deliberately avoids
`Finset.sum_range_succ`, whose proof closure (`Finset.notMem_range_self`) reaches the `Nat.Internal.Linear`
normaliser proofs that the Rocq importer cannot check in reasonable time. -/
theorem map_finRange_eq_map_range' (n : Nat) (f : Fin n → Nat) :
    (List.finRange n).map f = (List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else 0) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range']
  · intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h1
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range', Nat.zero_add, Nat.one_mul,
      Fin.cast_mk, dif_pos h1]

theorem production_fin_sum (n : Nat) (f : Fin n → Nat) :
    (∑ i : Fin n, f i) =
      List.foldr Nat.add 0 ((List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else 0)) := by
  rw [← map_finRange_eq_map_range']
  rfl

end Prosa.Validation.MultiprocessorInterface
