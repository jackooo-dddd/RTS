# `analysis/facts/transform/edf_wc.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `non_idle_swap_maintains_work_conservation_t1` | Lemma | `Prosa.Analysis.Facts.Transform.EdfWc.non_idle_swap_maintains_work_conservation_t1` | `non_idle_swap_maintains_work_conservation_t1_correspondence` | [view](3_printed_declarations/non_idle_swap_maintains_work_conservation_t1.md) |
| `non_idle_swap_maintains_work_conservation_t2` | Lemma | `Prosa.Analysis.Facts.Transform.EdfWc.non_idle_swap_maintains_work_conservation_t2` | `non_idle_swap_maintains_work_conservation_t2_correspondence` | [view](3_printed_declarations/non_idle_swap_maintains_work_conservation_t2.md) |
| `non_idle_swap_maintains_work_conservation_LEQ_t1` | Lemma | `Prosa.Analysis.Facts.Transform.EdfWc.non_idle_swap_maintains_work_conservation_LEQ_t1` | `non_idle_swap_maintains_work_conservation_LEQ_t1_correspondence` | [view](3_printed_declarations/non_idle_swap_maintains_work_conservation_LEQ_t1.md) |
| `non_idle_swap_maintains_work_conservation_GT_t2` | Lemma | `Prosa.Analysis.Facts.Transform.EdfWc.non_idle_swap_maintains_work_conservation_GT_t2` | `non_idle_swap_maintains_work_conservation_GT_t2_correspondence` | [view](3_printed_declarations/non_idle_swap_maintains_work_conservation_GT_t2.md) |
| `non_idle_swap_maintains_work_conservation_BET_t1_t2` | Lemma | `Prosa.Analysis.Facts.Transform.EdfWc.non_idle_swap_maintains_work_conservation_BET_t1_t2` | `non_idle_swap_maintains_work_conservation_BET_t1_t2_correspondence` | [view](3_printed_declarations/non_idle_swap_maintains_work_conservation_BET_t1_t2.md) |
| `fsc_swap_maintains_work_conservation` | Corollary | `Prosa.Analysis.Facts.Transform.EdfWc.fsc_swap_maintains_work_conservation` | `fsc_swap_maintains_work_conservation_correspondence` | [view](3_printed_declarations/fsc_swap_maintains_work_conservation.md) |
| `mea_maintains_work_conservation` | Lemma | `Prosa.Analysis.Facts.Transform.EdfWc.mea_maintains_work_conservation` | `mea_maintains_work_conservation_correspondence` | [view](3_printed_declarations/mea_maintains_work_conservation.md) |
| `scheduled_behavior_premises` | Definition | `Prosa.Analysis.Facts.Transform.EdfWc.scheduled_behavior_premises` | `scheduled_behavior_premises_correspondence` | [view](3_printed_declarations/scheduled_behavior_premises.md) |
| `edf_transform_prefix_maintains_work_conservation` | Lemma | `Prosa.Analysis.Facts.Transform.EdfWc.edf_transform_prefix_maintains_work_conservation` | `edf_transform_prefix_maintains_work_conservation_correspondence` | [view](3_printed_declarations/edf_transform_prefix_maintains_work_conservation.md) |
| `sched_satisfies_behavior_premises` | Lemma | `Prosa.Analysis.Facts.Transform.EdfWc.sched_satisfies_behavior_premises` | `sched_satisfies_behavior_premises_correspondence` | [view](3_printed_declarations/sched_satisfies_behavior_premises.md) |
| `edf_transform_maintains_work_conservation` | Lemma | `Prosa.Analysis.Facts.Transform.EdfWc.edf_transform_maintains_work_conservation` | `edf_transform_maintains_work_conservation_correspondence` | [view](3_printed_declarations/edf_transform_maintains_work_conservation.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsEdfOptCorrespondence`](4_correspondence/FactsEdfOptCorrespondence.v) | Helper-only copy of accepted certificates/analysis_facts_transform_edf_opt/FactsEdfOptCorrespondence.v: the imported module name differs and the statement correspondences (whose statements are not … |
| [`FactsEdfWcCorrespondence`](4_correspondence/FactsEdfWcCorrespondence.v) | Definition and statement correspondences for `analysis/facts/transform/edf_wc.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
