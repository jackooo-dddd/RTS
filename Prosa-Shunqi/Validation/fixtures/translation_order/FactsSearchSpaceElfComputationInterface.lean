import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Elf
import Validation.fixtures.translation_order.FactsElfAthepBoundComputationInterface
import Validation.fixtures.translation_order.BlockingBoundElfComputationInterface

/-!
Export root for `analysis/abstract/restricted_supply/search_space/elf.v`: the definition and the statement
together with the accepted ELF workload-bound facts export root (workloads, arrival curves, request-bound functions,
ELF/GEL, kernel-checked `Int` equations), the accepted ELF blocking-bound root (task preemption parameters,
conditional maxima), the accepted abstract search-space predicate, kernel-checked constructor equations for
`List.any` (as in the accepted EDF search space) and one kernel-checked `Int` disequality observation.
Every equation is proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.SearchSpaceElfInterface

universe u

theorem production_any_nil {X : Type u} (p : X → Bool) : ([] : List X).any p = false := rfl

theorem production_any_cons {X : Type u} (p : X → Bool) (x : X) (xs : List X) :
    (x :: xs).any p = (p x || xs.any p) := rfl

/-- Kernel-checked `Int` disequality observation through the order (proved in Lean, exported with
its proof). -/
theorem production_int_decide_ne (a b : Int) :
    decide (a ≠ b) = !(decide (a ≤ b) && decide (b ≤ a)) := by
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (a ≤ b ∧ b ≤ a) := fun ⟨h1, h2⟩ => h (Int.le_antisymm h1 h2)
    simp only [Bool.not_and]
    by_cases h1 : a ≤ b <;> by_cases h2 : b ≤ a <;> simp_all

end Prosa.Validation.SearchSpaceElfInterface
