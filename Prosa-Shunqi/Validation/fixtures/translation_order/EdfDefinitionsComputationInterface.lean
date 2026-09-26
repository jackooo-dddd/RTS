import Prosa.Analysis.Facts.EdfDefinitions
import Validation.fixtures.translation_order.IdealUniSchedulerComputationInterface
import Prosa.Implementation.Facts.IdealUni.PrioAware

/-!
Export root for `analysis/facts/edf_definitions.v`: the three statements
together with the accepted ideal-uniprocessor-scheduler export root
(preemption-parameter closure with the Service / Schedule interfaces, the ideal
processor with its kernel-checked ideal-state equations, readiness,
preemption-time and priority definitions, reached through the accepted
priority-aware scheduler facts module).  No new equation is added.
-/
