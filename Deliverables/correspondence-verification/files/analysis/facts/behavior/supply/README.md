# `analysis/facts/behavior/supply.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `service_at_le_supply_at` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.service_at_le_supply_at` | `fs_service_at_le_supply_at_correspondence` | [view](3_printed_declarations/service_at_le_supply_at.md) |
| `pos_service_impl_pos_supply` | Corollary | `Prosa.Analysis.Facts.Behavior.Supply.pos_service_impl_pos_supply` | `fs_pos_service_impl_pos_supply_correspondence` | [view](3_printed_declarations/pos_service_impl_pos_supply.md) |
| `blackout_or_supply` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.blackout_or_supply` | `fs_blackout_or_supply_correspondence` | [view](3_printed_declarations/blackout_or_supply.md) |
| `supply_at_complement` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.supply_at_complement` | `fs_supply_at_complement_correspondence` | [view](3_printed_declarations/supply_at_complement.md) |
| `is_blackout_complement` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.is_blackout_complement` | `fs_is_blackout_complement_correspondence` | [view](3_printed_declarations/is_blackout_complement.md) |
| `supply_at_le_1` | Remark | `Prosa.Analysis.Facts.Behavior.Supply.supply_at_le_1` | `fs_supply_at_le_1_correspondence` | [view](3_printed_declarations/supply_at_le_1.md) |
| `unit_supply_proc_service_case` | Corollary | `Prosa.Analysis.Facts.Behavior.Supply.unit_supply_proc_service_case` | `fs_unit_supply_proc_service_case_correspondence` | [view](3_printed_declarations/unit_supply_proc_service_case.md) |
| `supply_during_bound` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.supply_during_bound` | `fs_supply_during_bound_correspondence` | [view](3_printed_declarations/supply_during_bound.md) |
| `blackout_during_bound` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.blackout_during_bound` | `fs_blackout_during_bound_correspondence` | [view](3_printed_declarations/blackout_during_bound.md) |
| `supply_during_last_plus_before` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.supply_during_last_plus_before` | `fs_supply_during_last_plus_before_correspondence` | [view](3_printed_declarations/supply_during_last_plus_before.md) |
| `blackout_during_last_plus_before` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.blackout_during_last_plus_before` | `fs_blackout_during_last_plus_before_correspondence` | [view](3_printed_declarations/blackout_during_last_plus_before.md) |
| `supply_during_complement` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.supply_during_complement` | `fs_supply_during_complement_correspondence` | [view](3_printed_declarations/supply_during_complement.md) |
| `blackout_during_complement` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.blackout_during_complement` | `fs_blackout_during_complement_correspondence` | [view](3_printed_declarations/blackout_during_complement.md) |
| `blackout_during_cat` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.blackout_during_cat` | `fs_blackout_during_cat_correspondence` | [view](3_printed_declarations/blackout_during_cat.md) |
| `blackout_during_unit_growth` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.blackout_during_unit_growth` | `fs_blackout_during_unit_growth_correspondence` | [view](3_printed_declarations/blackout_during_unit_growth.md) |
| `progress_inside_supplies` | Lemma | `Prosa.Analysis.Facts.Behavior.Supply.progress_inside_supplies` | `fs_progress_inside_supplies_correspondence` | [view](3_printed_declarations/progress_inside_supplies.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsSupplyExactTypeGuards`](4_correspondence/FactsSupplyExactTypeGuards.v) | Convertibility guards are separated from certificates. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SchSourceTrue`, `SchTrue`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
