import Prosa.Analysis.Facts.Interference
import Validation.fixtures.translation_order.BusyIntervalClassicalComputationInterface
import Validation.fixtures.translation_order.WorkloadComputationInterface
import Validation.fixtures.translation_order.ServiceOfJobsComputationInterface
import Validation.fixtures.translation_order.InterferenceComputationInterface
import Validation.fixtures.translation_order.SupplyComputationInterface
import Validation.fixtures.translation_order.ScheduledComputationInterface

/-!
Export root for `analysis/facts/interference.v`: the 17 statements together
with the accepted busy-interval, workload, service-of-jobs and interference
export roots (preemption-parameter / Service closure) and the accepted
supply and scheduled-job interfaces (kernel-guarded supply projections and
`isEmpty` constructor equations).
-/
