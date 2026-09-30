import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace FinSumRepro

/-- control: a plain `Fin n` sum (uses `Fin.fintype n`). -/
def finSum (n : Nat) (f : Fin n → Nat) : Nat := ∑ i : Fin n, f i

/-- suspect: the Mathlib lemma used by the old `production_fin_sum` proof. -/
theorem suspect (m : Nat) (g : Nat → Nat) :
    (∑ i ∈ Finset.range (m + 1), g i) = (∑ i ∈ Finset.range m, g i) + g m :=
  Finset.sum_range_succ g m

end FinSumRepro
