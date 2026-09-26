import Prosa.Analysis.Facts.Model.Rbf
import Validation.fixtures.translation_order.WorkloadBoundedComputationInterface
import Validation.fixtures.translation_order.RequestBoundFunctionComputationInterface
import Validation.fixtures.translation_order.CurvesComputationInterface
import Validation.fixtures.translation_order.ProcessorStateCoverInterface

/-!
Export root for `analysis/facts/model/rbf.v`: the 27 statements together with
the accepted workload-bound (busy-interval + workload), request-bound-function
and arrival-curve export roots, over the preemption-parameter / Service
closure, and the accepted processor-state cover interface (processor models
quantified inside statements).
-/
