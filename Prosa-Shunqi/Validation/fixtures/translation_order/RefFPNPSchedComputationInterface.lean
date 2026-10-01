import Prosa.Implementation.Refinements.FP.NonpreemptiveSched
import Validation.fixtures.translation_order.RefSchedComputationInterface

/-!
Export root for `implementation/refinements/FP/nonpreemptive_sched.v`: its definitions and statements (statement-only) together with the accepted
ideal-uniprocessor-scheduler export root (the Service / Schedule interfaces, the ideal processor, the generic
scheduler, the work-conserving backlog, the scheduler definitions and the kernel-checked `schedule_up_to` /
`empty_schedule` / `replace_at` and ideal-state equations) and the accepted extrapolated-arrival-curve arithmetic
laws of the concrete task definitions, with the shared concrete-job instances of the accepted Bigcat and
ideal-uniprocessor-scheduler interface equations (`RefSchedComputationInterface`).  No new equation is added.
-/
