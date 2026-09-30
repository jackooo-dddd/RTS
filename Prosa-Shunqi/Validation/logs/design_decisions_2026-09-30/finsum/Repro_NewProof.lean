import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace FinSumRepro

theorem map_finRange_eq_map_range' (n : Nat) (f : Fin n → Nat) :
    (List.finRange n).map f = (List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else 0) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range']
  · intro i h1 h2
    simp only [List.length_map, List.length_finRange] at h1
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range', Nat.zero_add, Nat.one_mul, Fin.cast_mk,
      dif_pos h1]

theorem production_fin_sum (n : Nat) (f : Fin n → Nat) :
    (∑ i : Fin n, f i) =
      List.foldr Nat.add 0 ((List.range' 0 n).map (fun k => if h : k < n then f ⟨k, h⟩ else 0)) := by
  rw [← map_finRange_eq_map_range']
  rfl

end FinSumRepro
