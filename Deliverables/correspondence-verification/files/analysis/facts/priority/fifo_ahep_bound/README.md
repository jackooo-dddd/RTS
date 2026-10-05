# `analysis/facts/priority/fifo_ahep_bound.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `bound_on_hep_workload` | Lemma | `Prosa.Analysis.Facts.Priority.FifoAhepBound.bound_on_hep_workload` | `bound_on_hep_workload_correspondence` | [view](3_printed_declarations/bound_on_hep_workload.md) |

## Certificates

| Module | Role |
|---|---|
| [`FifoAhepBoundCorrespondence`](4_correspondence/FifoAhepBoundCorrespondence.v) | Statement correspondence for `analysis/facts/priority/fifo_ahep_bound.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
