# `model/readiness/suspension.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `JobSuspension` | Class | `Prosa.Model.Readiness.Suspension.JobSuspension` | `JobSuspension_source_total, JobSuspension_target_total` | [view](3_printed_declarations/JobSuspension.md) |
| `suspension_has_passed` | Definition | `Prosa.Model.Readiness.Suspension.suspension_has_passed` | `suspension_has_passed_correspondence` | [view](3_printed_declarations/suspension_has_passed.md) |
| `suspended` | Definition | `Prosa.Model.Readiness.Suspension.suspended` | `suspended_correspondence` | [view](3_printed_declarations/suspended.md) |
| `total_suspension` | Definition | `Prosa.Model.Readiness.Suspension.total_suspension` | `total_suspension_correspondence` | [view](3_printed_declarations/total_suspension.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
