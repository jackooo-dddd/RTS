# `analysis/facts/tdma.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `TDMA_cycle_ge_each_time_slot` | Lemma | `Prosa.Analysis.Facts.Tdma.TDMA_cycle_ge_each_time_slot` | `TDMA_cycle_ge_each_time_slot_correspondence` | [view](3_printed_declarations/TDMA_cycle_ge_each_time_slot.md) |
| `TDMA_cycle_positive` | Lemma | `Prosa.Analysis.Facts.Tdma.TDMA_cycle_positive` | `TDMA_cycle_positive_correspondence` | [view](3_printed_declarations/TDMA_cycle_positive.md) |
| `Offset_lt_cycle` | Lemma | `Prosa.Analysis.Facts.Tdma.Offset_lt_cycle` | `Offset_lt_cycle_correspondence` | [view](3_printed_declarations/Offset_lt_cycle.md) |
| `Offset_add_slot_leq_cycle` | Lemma | `Prosa.Analysis.Facts.Tdma.Offset_add_slot_leq_cycle` | `Offset_add_slot_leq_cycle_correspondence` | [view](3_printed_declarations/Offset_add_slot_leq_cycle.md) |
| `relation_offset` | Lemma | `Prosa.Analysis.Facts.Tdma.relation_offset` | `relation_offset_correspondence` | [view](3_printed_declarations/relation_offset.md) |
| `task_in_time_slot_uniq` | Lemma | `Prosa.Analysis.Facts.Tdma.task_in_time_slot_uniq` | `task_in_time_slot_uniq_correspondence` | [view](3_printed_declarations/task_in_time_slot_uniq.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsTdmaCorrespondence`](4_correspondence/FactsTdmaCorrespondence.v) | Statement correspondences for `analysis/facts/tdma.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
