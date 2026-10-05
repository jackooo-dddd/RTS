# `model/task/absolute_deadline.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_deadline_from_task_deadline` | Instance | `Prosa.Model.Task.AbsoluteDeadline.job_deadline_from_task_deadline` | `ad_job_deadline_from_task_deadline_certificate` | [view](3_printed_declarations/job_deadline_from_task_deadline.md) |

## Certificates

| Module | Role |
|---|---|
| [`AbsoluteDeadlineBaseAdapter`](4_correspondence/AbsoluteDeadlineBaseAdapter.v) | Artifact-local field adapters for the actual ImportedAbsoluteDeadline records. |
| [`AbsoluteDeadlineCorrespondence`](4_correspondence/AbsoluteDeadlineCorrespondence.v) | The certificate composes three related class observations with the already certified Nat-add operation. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | — |
| Imported Lean axioms | — |
| Definitional UIP | `eq` |
| Rocq primitives | — |
