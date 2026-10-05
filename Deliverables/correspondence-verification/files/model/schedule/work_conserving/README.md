# `model/schedule/work_conserving.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `work_conserving` | Definition | `Prosa.Model.Schedule.WorkConserving.work_conserving` | `work_conserving_correspondence` | [view](3_printed_declarations/work_conserving.md) |
| `jobs_backlogged_at` | Definition | `Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at` | `jobs_backlogged_at_correspondence` | [view](3_printed_declarations/jobs_backlogged_at.md) |

## Certificates

| Module | Role |
|---|---|
| [`WorkConservingExactTypeGuards`](4_correspondence/WorkConservingExactTypeGuards.v) | Full elaborated public types: source has no equality-instance binder, target includes its explicit DecidableEq binder. |
| [`ReadyArrivalCorrespondence`](4_correspondence/ReadyArrivalCorrespondence.v) | Fourteen compositional certificates for the official v0.6 definitions and the actual imported production Lean bodies. |
| [`WorkConservingCorrespondence`](4_correspondence/WorkConservingCorrespondence.v) | The two official v0.6 work-conserving declarations, related to the actual imported Lean bodies. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
