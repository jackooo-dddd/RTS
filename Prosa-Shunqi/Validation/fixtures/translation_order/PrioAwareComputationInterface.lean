import Prosa.Implementation.Facts.IdealUni.PrioAware
import Validation.fixtures.translation_order.IdealUniSchedulerComputationInterface

/-!
Export root for `implementation/facts/ideal_uni/prio_aware.v`: the five
statements together with the accepted ideal-uniprocessor-scheduler export root
(preemption-parameter closure with the Service / Schedule interfaces, the ideal
processor, the generic scheduler, the work-conserving backlog, the scheduler
definitions and the kernel-checked `schedule_up_to`/`empty_schedule`/
`replace_at` and ideal-state equations).  No new equation is added.
-/
