import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fifo
import Validation.fixtures.translation_order.FactsSearchSpaceFpComputationInterface

/-!
Export root for `analysis/abstract/restricted_supply/search_space/fifo.v`: the definition and the statement
together with the accepted FP search-space export root (request-bound functions, arrival curves, the abstract
search-space predicate), the supply-bound-function class of the accepted `analysis/definitions/sbf` translation
(reached through the statement) and kernel-checked constructor equations for `List.any` (as in the accepted EDF
and ELF search spaces). Every equation is proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.SearchSpaceFifoInterface

universe u

theorem production_any_nil {X : Type u} (p : X → Bool) : ([] : List X).any p = false := rfl

theorem production_any_cons {X : Type u} (p : X → Bool) (x : X) (xs : List X) :
    (x :: xs).any p = (p x || xs.any p) := rfl

end Prosa.Validation.SearchSpaceFifoInterface
