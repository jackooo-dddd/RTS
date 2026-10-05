# `model/schedule/edf.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `EDF_at` | Definition | `Prosa.Model.Schedule.Edf.EDF_at` | `EDF_at_correspondence` | [view](3_printed_declarations/EDF_at.md) |
| `EDF_schedule` | Definition | `Prosa.Model.Schedule.Edf.EDF_schedule` | `EDF_schedule_correspondence` | [view](3_printed_declarations/EDF_schedule.md) |

## Certificates

| Module | Role |
|---|---|
| [`EdfBaseAdapter`](4_correspondence/EdfBaseAdapter.v) | Artifact-local Bool/equality adapter for the actual imported EDF module. |
| [`EdfExactTypeGuards`](4_correspondence/EdfExactTypeGuards.v) | No description in the module. |
| [`EdfOperations`](4_correspondence/EdfOperations.v) | Only the already certified finite scheduled-in truth interface and the state/core observations actually consumed by EDF are used below. |
| [`EdfCorrespondence`](4_correspondence/EdfCorrespondence.v) | Field observations required by the source classes and their actual imported Lean counterparts. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `EdfSourceTrue`, `EdfTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
