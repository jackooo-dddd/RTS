# `analysis/definitions/workload/elf_athep_bound.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `ep_task_interfering_interval_length` | Definition | `Prosa.Analysis.Definitions.Workload.ElfAthepBound.ep_task_interfering_interval_length` | `ep_task_interfering_interval_length_correspondence` | [view](3_printed_declarations/ep_task_interfering_interval_length.md) |
| `bound_on_ep_task_workload` | Definition | `Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_ep_task_workload` | `bound_on_ep_task_workload_correspondence` | [view](3_printed_declarations/bound_on_ep_task_workload.md) |
| `bound_on_hp_task_workload` | Definition | `Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_hp_task_workload` | `bound_on_hp_task_workload_correspondence` | [view](3_printed_declarations/bound_on_hp_task_workload.md) |
| `bound_on_athep_workload` | Definition | `Prosa.Analysis.Definitions.Workload.ElfAthepBound.bound_on_athep_workload` | `bound_on_athep_workload_correspondence` | [view](3_printed_declarations/bound_on_athep_workload.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
