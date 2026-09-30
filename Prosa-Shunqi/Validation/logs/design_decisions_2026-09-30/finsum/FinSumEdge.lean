import Validation.fixtures.translation_order.MultiprocessorComputationInterface
open scoped BigOperators
open Prosa.Validation.MultiprocessorInterface
-- n = 0: both sides are 0 for every f
example (f : Fin 0 → Nat) : (∑ i : Fin 0, f i) = 0 := by rw [production_fin_sum]; rfl
-- n = 1: both sides are f 0
example (f : Fin 1 → Nat) : (∑ i : Fin 1, f i) = f 0 := by rw [production_fin_sum]; rfl
-- n = 3 on a concrete family
example : (∑ i : Fin 3, ((i : Nat) + 1)) = 6 := by rw [production_fin_sum]; decide
#print axioms production_fin_sum
