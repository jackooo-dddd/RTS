import Prosa.Analysis.Facts.Jitter
import Validation.fixtures.translation_order.FactsPreemptionComputationInterface
import Validation.fixtures.translation_order.FactsDelayPropagationComputationInterface
import Validation.fixtures.translation_order.SchedulabilityComputationInterface

/-!
Export root for `analysis/facts/jitter.v`: the fourteen statements and the local helpers
`release_as_arrival` / `release_curve`, together with the accepted preemption-facts export root (processor-state
cover, priority-driven schedules, preemption times), the accepted delay-propagation facts export root and the
accepted schedulability export root. No new equation is added.
-/
