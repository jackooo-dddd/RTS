import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Edf
import Validation.fixtures.translation_order.WorkloadBoundedComputationInterface
import Validation.fixtures.translation_order.RequestBoundFunctionComputationInterface
import Validation.fixtures.translation_order.CurvesComputationInterface
import Validation.fixtures.translation_order.ProcessorStateCoverInterface
import Validation.fixtures.translation_order.EdfAthepBoundComputationInterface
import Validation.fixtures.translation_order.BlockingBoundEdfComputationInterface

/-!
Export root for `analysis/abstract/restricted_supply/search_space/edf.v`: the
definition and the statement together with the accepted workload-bound,
request-bound-function, arrival-curve and EDF athep-bound definition export
roots (over the preemption-parameter / Service closure), the accepted
task-preemption-parameter and EDF blocking-bound roots, the accepted abstract
search-space predicate, and kernel-checked constructor equations for
`List.any`.  Every equation is proved in Lean and exported with its proof.
-/

namespace Prosa.Validation.SearchSpaceEdfInterface

universe u

theorem production_any_nil {X : Type u} (p : X → Bool) : ([] : List X).any p = false := rfl

theorem production_any_cons {X : Type u} (p : X → Bool) (x : X) (xs : List X) :
    (x :: xs).any p = (p x || xs.any p) := rfl

end Prosa.Validation.SearchSpaceEdfInterface
