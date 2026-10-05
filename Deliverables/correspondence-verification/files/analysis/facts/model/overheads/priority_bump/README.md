# `analysis/facts/model/overheads/priority_bump.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `priority_bump_implies_preemption_time` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.PriorityBump.priority_bump_implies_preemption_time` | `priority_bump_implies_preemption_time_correspondence` | [view](3_printed_declarations/priority_bump_implies_preemption_time.md) |
| `priority_bump_implies_hp_arrival_in_prefix` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.PriorityBump.priority_bump_implies_hp_arrival_in_prefix` | `priority_bump_implies_hp_arrival_in_prefix_correspondence` | [view](3_printed_declarations/priority_bump_implies_hp_arrival_in_prefix.md) |
| `no_priority_bumps_in_fifo` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.PriorityBump.no_priority_bumps_in_fifo` | `no_priority_bumps_in_fifo_correspondence` | [view](3_printed_declarations/no_priority_bumps_in_fifo.md) |

## Certificates

| Module | Role |
|---|---|
| [`OverheadsPriorityBumpFactsCorrespondence`](4_correspondence/OverheadsPriorityBumpFactsCorrespondence.v) | Statement correspondences for `analysis/facts/model/overheads/priority_bump.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
