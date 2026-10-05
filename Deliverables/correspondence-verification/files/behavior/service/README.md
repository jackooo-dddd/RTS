# `behavior/service.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `scheduled_at` | Definition | `Prosa.Behavior.Service.scheduled_at` | `` | [view](3_printed_declarations/scheduled_at.md) |
| `service_at` | Definition | `Prosa.Behavior.Service.service_at` | `` | [view](3_printed_declarations/service_at.md) |
| `receives_service_at` | Definition | `Prosa.Behavior.Service.receives_service_at` | `` | [view](3_printed_declarations/receives_service_at.md) |
| `service_during` | Definition | `Prosa.Behavior.Service.service_during` | `` | [view](3_printed_declarations/service_during.md) |
| `service` | Definition | `Prosa.Behavior.Service.service` | `` | [view](3_printed_declarations/service.md) |
| `completed_by` | Definition | `Prosa.Behavior.Service.completed_by` | `` | [view](3_printed_declarations/completed_by.md) |
| `completes_at` | Definition | `Prosa.Behavior.Service.completes_at` | `` | [view](3_printed_declarations/completes_at.md) |
| `job_response_time_bound` | Definition | `Prosa.Behavior.Service.job_response_time_bound` | `` | [view](3_printed_declarations/job_response_time_bound.md) |
| `job_meets_deadline` | Definition | `Prosa.Behavior.Service.job_meets_deadline` | `` | [view](3_printed_declarations/job_meets_deadline.md) |
| `pending` | Definition | `Prosa.Behavior.Service.pending` | `` | [view](3_printed_declarations/pending.md) |
| `pending_earlier_and_at` | Definition | `Prosa.Behavior.Service.pending_earlier_and_at` | `` | [view](3_printed_declarations/pending_earlier_and_at.md) |
| `remaining_cost` | Definition | `Prosa.Behavior.Service.remaining_cost` | `` | [view](3_printed_declarations/remaining_cost.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
