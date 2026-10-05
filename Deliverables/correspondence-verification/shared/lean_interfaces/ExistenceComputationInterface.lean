import Prosa.Analysis.Facts.BusyInterval.Existence
import Validation.fixtures.translation_order.FactsPreemptionComputationInterface
import Validation.fixtures.translation_order.BusyIntervalClassicalComputationInterface
import Validation.fixtures.translation_order.FactsServiceOfJobsComputationInterface
import Validation.fixtures.translation_order.PriorityInversionComputationInterface
import Validation.fixtures.translation_order.WorkBearingReadinessComputationInterface
import Validation.fixtures.translation_order.JobPropertiesExportInterface

/-!
Export root for `analysis/facts/busy_interval/existence.v`: the fourteen
statements together with the accepted preemption-facts export root, the
accepted classical busy-interval export root, the accepted service-of-jobs /
workload export root, the accepted priority-inversion export root, the
accepted work-bearing-readiness export root and the accepted job-properties
export root.  No statement contains a raw interval sum, so no normalization
guard is needed.
-/
