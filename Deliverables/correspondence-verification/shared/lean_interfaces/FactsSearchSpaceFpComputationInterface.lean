import Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.Fp
import Validation.fixtures.translation_order.WorkloadBoundedComputationInterface
import Validation.fixtures.translation_order.RequestBoundFunctionComputationInterface
import Validation.fixtures.translation_order.CurvesComputationInterface
import Validation.fixtures.translation_order.ProcessorStateCoverInterface
import Validation.fixtures.translation_order.BlockingBoundFpComputationInterface

/-!
Export root for `analysis/abstract/restricted_supply/search_space/fp.v`: the
definition and the statement together with the accepted workload-bound,
request-bound-function and arrival-curve export roots (over the
preemption-parameter / Service closure), the accepted task-preemption-parameter
and EDF/FP blocking-bound roots (with their `bigMaxListCond` equations), and
the accepted abstract search-space predicate.
-/
