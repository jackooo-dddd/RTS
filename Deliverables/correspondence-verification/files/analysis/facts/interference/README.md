# `analysis/facts/interference.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `another_task_hep_job_split_hp_ep` | Lemma | `Prosa.Analysis.Facts.Interference.another_task_hep_job_split_hp_ep` | `another_task_hep_job_split_hp_ep_correspondence` | [view](3_printed_declarations/another_task_hep_job_split_hp_ep.md) |
| `hep_interference_another_task_split` | Lemma | `Prosa.Analysis.Facts.Interference.hep_interference_another_task_split` | `hep_interference_another_task_split_correspondence` | [view](3_printed_declarations/hep_interference_another_task_split.md) |
| `cumulative_hep_interference_split_tasks_new` | Lemma | `Prosa.Analysis.Facts.Interference.cumulative_hep_interference_split_tasks_new` | `cumulative_hep_interference_split_tasks_new_correspondence` | [view](3_printed_declarations/cumulative_hep_interference_split_tasks_new.md) |
| `no_hep_job_interference_without_supply` | Lemma | `Prosa.Analysis.Facts.Interference.no_hep_job_interference_without_supply` | `no_hep_job_interference_without_supply_correspondence` | [view](3_printed_declarations/no_hep_job_interference_without_supply.md) |
| `no_hep_task_interference_without_supply` | Lemma | `Prosa.Analysis.Facts.Interference.no_hep_task_interference_without_supply` | `no_hep_task_interference_without_supply_correspondence` | [view](3_printed_declarations/no_hep_task_interference_without_supply.md) |
| `no_hep_job_interference_when_idle` | Lemma | `Prosa.Analysis.Facts.Interference.no_hep_job_interference_when_idle` | `no_hep_job_interference_when_idle_correspondence` | [view](3_printed_declarations/no_hep_job_interference_when_idle.md) |
| `no_hep_task_interference_when_idle` | Lemma | `Prosa.Analysis.Facts.Interference.no_hep_task_interference_when_idle` | `no_hep_task_interference_when_idle_correspondence` | [view](3_printed_declarations/no_hep_task_interference_when_idle.md) |
| `interference_ahep_def` | Lemma | `Prosa.Analysis.Facts.Interference.interference_ahep_def` | `interference_ahep_def_correspondence` | [view](3_printed_declarations/interference_ahep_def.md) |
| `interference_athep_def` | Lemma | `Prosa.Analysis.Facts.Interference.interference_athep_def` | `interference_athep_def_correspondence` | [view](3_printed_declarations/interference_athep_def.md) |
| `no_ahep_interference_when_scheduled` | Lemma | `Prosa.Analysis.Facts.Interference.no_ahep_interference_when_scheduled` | `no_ahep_interference_when_scheduled_correspondence` | [view](3_printed_declarations/no_ahep_interference_when_scheduled.md) |
| `no_ahep_interference_when_served` | Lemma | `Prosa.Analysis.Facts.Interference.no_ahep_interference_when_served` | `no_ahep_interference_when_served_correspondence` | [view](3_printed_declarations/no_ahep_interference_when_served.md) |
| `no_athep_interference_when_scheduled` | Lemma | `Prosa.Analysis.Facts.Interference.no_athep_interference_when_scheduled` | `no_athep_interference_when_scheduled_correspondence` | [view](3_printed_declarations/no_athep_interference_when_scheduled.md) |
| `athep_interference_iff` | Lemma | `Prosa.Analysis.Facts.Interference.athep_interference_iff` | `athep_interference_iff_correspondence` | [view](3_printed_declarations/athep_interference_iff.md) |
| `athep_interference_if` | Lemma | `Prosa.Analysis.Facts.Interference.athep_interference_if` | `athep_interference_if_correspondence` | [view](3_printed_declarations/athep_interference_if.md) |
| `no_ahep_interference_when_scheduled_lp` | Lemma | `Prosa.Analysis.Facts.Interference.no_ahep_interference_when_scheduled_lp` | `no_ahep_interference_when_scheduled_lp_correspondence` | [view](3_printed_declarations/no_ahep_interference_when_scheduled_lp.md) |
| `cumulative_i_ohep_eq_service_of_ohep` | Lemma | `Prosa.Analysis.Facts.Interference.cumulative_i_ohep_eq_service_of_ohep` | `cumulative_i_ohep_eq_service_of_ohep_correspondence` | [view](3_printed_declarations/cumulative_i_ohep_eq_service_of_ohep.md) |
| `cumulative_i_thep_eq_service_of_othep` | Lemma | `Prosa.Analysis.Facts.Interference.cumulative_i_thep_eq_service_of_othep` | `cumulative_i_thep_eq_service_of_othep_correspondence` | [view](3_printed_declarations/cumulative_i_thep_eq_service_of_othep.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsInterferenceCorrespondence`](4_correspondence/FactsInterferenceCorrespondence.v) | Statement correspondences for `analysis/facts/interference.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
