# `model/priority/gel.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `offset` | Definition | `Prosa.Model.Priority.Gel.offset` | `offset_rocq_roundtrip_certificate, offset_imported_roundtrip_certificate` | [view](3_printed_declarations/offset.md) |
| `PriorityPoint` | Class | `Prosa.Model.Priority.Gel.PriorityPoint` | `PriorityPoint_source_total, PriorityPoint_target_total` | [view](3_printed_declarations/PriorityPoint.md) |
| `job_priority_point` | Definition | `Prosa.Model.Priority.Gel.job_priority_point` | `job_priority_point_correspondence` | [view](3_printed_declarations/job_priority_point.md) |
| `GEL` | Instance | `Prosa.Model.Priority.Gel.GEL` | `GEL_correspondence` | [view](3_printed_declarations/GEL.md) |
| `GEL_is_reflexive` | Fact | `Prosa.Model.Priority.Gel.GEL_is_reflexive` | `GEL_is_reflexive_correspondence` | [view](3_printed_declarations/GEL_is_reflexive.md) |
| `GEL_is_transitive` | Fact | `Prosa.Model.Priority.Gel.GEL_is_transitive` | `GEL_is_transitive_correspondence` | [view](3_printed_declarations/GEL_is_transitive.md) |
| `GEL_is_total` | Fact | `Prosa.Model.Priority.Gel.GEL_is_total` | `GEL_is_total_correspondence` | [view](3_printed_declarations/GEL_is_total.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `PdTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
