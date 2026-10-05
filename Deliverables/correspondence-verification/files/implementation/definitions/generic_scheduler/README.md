# `implementation/definitions/generic_scheduler.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `PointwisePolicy` | Definition | `Prosa.Implementation.Definitions.GenericScheduler.PointwisePolicy` | `gs_pointwise_policy_application` | [view](3_printed_declarations/PointwisePolicy.md) |
| `empty_schedule` | Definition | `Prosa.Implementation.Definitions.GenericScheduler.empty_schedule` | `gs_empty_schedule_correspondence` | [view](3_printed_declarations/empty_schedule.md) |
| `schedule_up_to` | Fixpoint | `Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to` | `gs_prefix_correspondence` | [view](3_printed_declarations/schedule_up_to.md) |
| `generic_schedule` | Definition | `Prosa.Implementation.Definitions.GenericScheduler.generic_schedule` | `gs_generic_schedule_correspondence` | [view](3_printed_declarations/generic_schedule.md) |

## Certificates

| Module | Role |
|---|---|
| [`GenericSchedulerBaseAdapter`](4_correspondence/GenericSchedulerBaseAdapter.v) | Artifact-local instantiation of the accepted Swap Nat/equality adapter. |
| [`GenericSchedulerExactTypeGuards`](4_correspondence/GenericSchedulerExactTypeGuards.v) | Proves or defines `gs_pointwise_policy_exact_type`, `gs_empty_schedule_exact_type`, `gs_schedule_up_to_exact_type` and 1 more. |
| [`GenericSchedulerOperations`](4_correspondence/GenericSchedulerOperations.v) | Proves or defines `gs_empty_schedule_correspondence`, `gs_replace_at_correspondence`. |
| [`GenericSchedulerRecursionEquations`](4_correspondence/GenericSchedulerRecursionEquations.v) | Kernel equations for the actual imported `Nat_brecOn` body. |
| [`GenericSchedulerCorrespondence`](4_correspondence/GenericSchedulerCorrespondence.v) | The public pointwise-policy definition unfolds to exactly the schedule-prefix/time-to-state function space on both sides. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
