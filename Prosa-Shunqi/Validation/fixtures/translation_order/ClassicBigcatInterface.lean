import Prosa.Classic.Util.Bigcat
import Mathlib.Algebra.BigOperators.Fin

/-!
Validation-only interface for `classic/util/bigcat.v` (classic family): kernel-checked Lean
equations, exported with their proofs, that read the ordinal-indexed concatenation
`Prosa.Util.Bigcat.bigCatFin` and the finite sum over `Fin n` as list operations over
`List.range' 0 n` (each ordinal visited through its value), which the Rocq certificate relates
structurally to MathComp's `iota 0 n`.  Used as propositional equations (transport) only.
The proofs follow the accepted v0.6 `MultiprocessorComputationInterface`.
-/

open scoped BigOperators

namespace Prosa.Validation.ClassicBigcatInterface

universe u

theorem map_finRange_eq_map_range' {α : Type u} (n : Nat) (f : Fin n → α) (d : α) :
    (List.finRange n).map f = (List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else d) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range']
  · intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h1
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range', Nat.zero_add, Nat.one_mul,
      Fin.cast_mk, dif_pos h1]

theorem bigCatFin_range' {α : Type u} (n : Nat) (f : Fin n → List α) :
    Prosa.Util.Bigcat.bigCatFin f =
      ((List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else [])).flatten := by
  rw [← map_finRange_eq_map_range']
  unfold Prosa.Util.Bigcat.bigCatFin
  rw [List.ofFn_eq_map]

theorem fin_sum_range' (n : Nat) (f : Fin n → Nat) :
    (∑ i : Fin n, f i) =
      List.foldr Nat.add 0 ((List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else 0)) := by
  rw [← map_finRange_eq_map_range']
  rfl

end Prosa.Validation.ClassicBigcatInterface
