import Prosa.Analysis.Facts.Model.Preemption
import Validation.fixtures.translation_order.PriorityDrivenComputationInterface
import Validation.fixtures.translation_order.ScheduledComputationInterface
import Validation.fixtures.translation_order.ProcessorStateCoverInterface

/-!
Export root for `analysis/facts/model/preemption.v`: the fourteen statements
together with the accepted priority-driven export root (preemption time,
scheduled jobs, preemption parameters and priority coercions) and the
readiness, validity and idleness definitions they mention, with the accepted
scheduled-jobs list equations and processor-model cover interface.  No new equation
is added.
-/
