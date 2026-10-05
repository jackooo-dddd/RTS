# `analysis/definitions/tardiness.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_tardiness_is_bounded` | Definition | `Prosa.Analysis.Definitions.Tardiness.task_tardiness_is_bounded` | `task_tardiness_is_bounded_correspondence` | [view](3_printed_declarations/task_tardiness_is_bounded.md) |

## Certificates

| Module | Role |
|---|---|
| [`TardinessCorrespondence`](4_correspondence/TardinessCorrespondence.v) | Definition certificate for `analysis/definitions/tardiness.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
