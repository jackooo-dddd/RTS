# `analysis/definitions/overheads/schedule_change.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `schedule_change` | Definition | `Prosa.Analysis.Definitions.Overheads.ScheduleChange.schedule_change` | `schedule_change_correspondence` | [view](3_printed_declarations/schedule_change.md) |
| `number_schedule_changes` | Definition | `Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes` | `number_schedule_changes_correspondence` | [view](3_printed_declarations/number_schedule_changes.md) |
| `no_schedule_changes_during` | Definition | `Prosa.Analysis.Definitions.Overheads.ScheduleChange.no_schedule_changes_during` | `no_schedule_changes_during_correspondence` | [view](3_printed_declarations/no_schedule_changes_during.md) |
| `scheduled_job_invariant` | Definition | `Prosa.Analysis.Definitions.Overheads.ScheduleChange.scheduled_job_invariant` | `scheduled_job_invariant_correspondence` | [view](3_printed_declarations/scheduled_job_invariant.md) |

## Certificates

| Module | Role |
|---|---|
| [`ScheduleChangeExactTypeGuards`](4_correspondence/ScheduleChangeExactTypeGuards.v) | No description in the module. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
