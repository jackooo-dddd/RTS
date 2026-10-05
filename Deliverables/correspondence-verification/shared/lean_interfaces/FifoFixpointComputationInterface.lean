import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.FifoFixpoint
import Validation.fixtures.translation_order.BoundedBiJlfpComputationInterface
import Validation.fixtures.translation_order.FactsSearchSpaceFifoComputationInterface

/-!
Export root for `analysis/abstract/restricted_supply/search_space/fifo_fixpoint.v`: the statement together with
the accepted restricted-supply JLFP bounded-busy-interval export root (classical busy-SBF, supply-bound-function
predicates, request-bound functions, task preemption parameters) and the accepted FIFO search-space root (its
definition and kernel-checked `List.any` equations); the FIFO policy is reached through the statement. No new
equation is added.
-/
