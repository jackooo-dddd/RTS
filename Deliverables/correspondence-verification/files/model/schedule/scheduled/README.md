# `model/schedule/scheduled.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `scheduled_jobs_at` | Definition | `Prosa.Model.Schedule.Scheduled.scheduled_jobs_at` | `scheduled_jobs_at_correspondence` | [view](3_printed_declarations/scheduled_jobs_at.md) |
| `scheduled_job_at` | Definition | `Prosa.Model.Schedule.Scheduled.scheduled_job_at` | `scheduled_job_at_correspondence` | [view](3_printed_declarations/scheduled_job_at.md) |
| `is_idle` | Definition | `Prosa.Model.Schedule.Scheduled.is_idle` | `is_idle_correspondence` | [view](3_printed_declarations/is_idle.md) |

## Certificates

| Module | Role |
|---|---|
| [`ScheduledExactTypeGuards`](4_correspondence/ScheduledExactTypeGuards.v) | No description in the module. |
| [`ScheduledStateBaseAdapter`](4_correspondence/ScheduledStateBaseAdapter.v) | Adapted from accepted EdfBaseAdapter.v (SHA-256 4916a4a40d389d79b806d3b71986b8c5c5d413c239b655fb6202f8e1c24122ef). |
| [`ReadyArrivalCorrespondence`](4_correspondence/ReadyArrivalCorrespondence.v) | Fourteen compositional certificates for the official v0.6 definitions and the actual imported production Lean bodies. |
| [`ScheduledStateOperations`](4_correspondence/ScheduledStateOperations.v) | Only the already certified finite scheduled-in truth interface and the state/core observations actually consumed by Scheduled are used below. |
| [`ScheduledCorrespondence`](4_correspondence/ScheduledCorrespondence.v) | Recover the imported Boolean value from its certified truth observation. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `EdfSourceTrue`, `EdfTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
