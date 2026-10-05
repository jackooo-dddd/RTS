# `model/task/jitter.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `TaskJitter` | Class | `Prosa.Model.Task.Jitter.TaskJitter` | `TaskJitter_source_total, TaskJitter_target_total, TaskJitter_source_roundtrip` | [view](3_printed_declarations/TaskJitter.md) |
| `valid_jitter` | Definition | `Prosa.Model.Task.Jitter.valid_jitter` | `valid_jitter_correspondence` | [view](3_printed_declarations/valid_jitter.md) |
| `valid_jitter_bounds` | Definition | `Prosa.Model.Task.Jitter.valid_jitter_bounds` | `valid_jitter_bounds_correspondence` | [view](3_printed_declarations/valid_jitter_bounds.md) |

## Certificates

| Module | Role |
|---|---|
| [`TaskJitterCorrespondence`](4_correspondence/TaskJitterCorrespondence.v) | Correspondence certificates for `model/task/jitter.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
