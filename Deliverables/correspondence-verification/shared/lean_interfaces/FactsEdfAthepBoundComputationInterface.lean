import Prosa.Analysis.Facts.Workload.EdfAthepBound
import Validation.fixtures.translation_order.WorkloadBoundedComputationInterface
import Validation.fixtures.translation_order.RequestBoundFunctionComputationInterface
import Validation.fixtures.translation_order.CurvesComputationInterface
import Validation.fixtures.translation_order.ProcessorStateCoverInterface
import Validation.fixtures.translation_order.EdfAthepBoundComputationInterface

/-!
Export root for `analysis/facts/workload/edf_athep_bound.v`: the 4 statements
together with the accepted workload-bound (busy-interval + workload),
request-bound-function, arrival-curve and EDF athep-bound definition export
roots (the latter with its kernel-checked `min` case equations), over the
preemption-parameter / Service closure, and the accepted processor-state cover
interface.
-/
