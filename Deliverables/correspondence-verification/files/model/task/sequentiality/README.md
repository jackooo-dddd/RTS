# `model/task/sequentiality.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `sequential_tasks` | Definition | `Prosa.Model.Task.Sequentiality.sequential_tasks` | `sequential_tasks_correspondence` | [view](3_printed_declarations/sequential_tasks.md) |
| `prior_jobs_complete` | Definition | `Prosa.Model.Task.Sequentiality.prior_jobs_complete` | `prior_jobs_complete_correspondence` | [view](3_printed_declarations/prior_jobs_complete.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
