# `behavior/job.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `JobType` | Definition | `Prosa.Behavior.Job.JobType` | `` | [view](3_printed_declarations/JobType.md) |
| `work` | Definition | `Prosa.Behavior.Job.work` | `` | [view](3_printed_declarations/work.md) |
| `JobCost` | Class | `Prosa.Behavior.Job.JobCost` | `` | [view](3_printed_declarations/JobCost.md) |
| `JobArrival` | Class | `Prosa.Behavior.Job.JobArrival` | `` | [view](3_printed_declarations/JobArrival.md) |
| `JobDeadline` | Class | `Prosa.Behavior.Job.JobDeadline` | `` | [view](3_printed_declarations/JobDeadline.md) |

## Certificates

| Module | Role |
|---|---|
| [`JobCorrespondence`](4_correspondence/JobCorrespondence.v) | The actual imported Lean aliases `JobType`, `work`, and `instant` reduce to the carrier `Type` and imported `Nat`, respectively. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | — |
| Imported Lean axioms | — |
| Definitional UIP | `JobEqObservationTrue`, `eq` |
| Rocq primitives | — |
