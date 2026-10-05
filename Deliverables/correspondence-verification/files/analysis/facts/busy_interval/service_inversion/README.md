# `analysis/facts/busy_interval/service_inversion.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `blackout_implies_no_service_inversion` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.blackout_implies_no_service_inversion` | `blackout_implies_no_service_inversion_correspondence` | [view](3_printed_declarations/blackout_implies_no_service_inversion.md) |
| `idle_implies_no_service_inversion` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.idle_implies_no_service_inversion` | `idle_implies_no_service_inversion_correspondence` | [view](3_printed_declarations/idle_implies_no_service_inversion.md) |
| `receives_service_implies_no_service_inversion` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.receives_service_implies_no_service_inversion` | `receives_service_implies_no_service_inversion_correspondence` | [view](3_printed_declarations/receives_service_implies_no_service_inversion.md) |
| `service_inversion_cat` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_cat` | `service_inversion_cat_correspondence` | [view](3_printed_declarations/service_inversion_cat.md) |
| `service_inversion_widen` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_widen` | `service_inversion_widen_correspondence` | [view](3_printed_declarations/service_inversion_widen.md) |
| `service_inversion_supply_sched` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_supply_sched` | `service_inversion_supply_sched_correspondence` | [view](3_printed_declarations/service_inversion_supply_sched.md) |
| `service_inv_implies_priority_inv` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inv_implies_priority_inv` | `service_inv_implies_priority_inv_correspondence` | [view](3_printed_declarations/service_inv_implies_priority_inv.md) |
| `cumul_service_inv_le_cumul_priority_inv` | Corollary | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.cumul_service_inv_le_cumul_priority_inv` | `cumul_service_inv_le_cumul_priority_inv_correspondence` | [view](3_printed_declarations/cumul_service_inv_le_cumul_priority_inv.md) |
| `cumulative_service_inversion_from_one_job` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.cumulative_service_inversion_from_one_job` | `cumulative_service_inversion_from_one_job_correspondence` | [view](3_printed_declarations/cumulative_service_inversion_from_one_job.md) |
| `lp_job_bounded_service` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.lp_job_bounded_service` | `lp_job_bounded_service_correspondence` | [view](3_printed_declarations/lp_job_bounded_service.md) |
| `lp_job_bounded_service_max` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.lp_job_bounded_service_max` | `lp_job_bounded_service_max_correspondence` | [view](3_printed_declarations/lp_job_bounded_service_max.md) |
| `service_inversion_is_bounded` | Lemma | `Prosa.Analysis.Facts.BusyInterval.ServiceInversion.service_inversion_is_bounded` | `service_inversion_is_bounded_correspondence` | [view](3_printed_declarations/service_inversion_is_bounded.md) |

## Certificates

| Module | Role |
|---|---|
| [`BusyIntervalServiceInversionCorrespondence`](4_correspondence/BusyIntervalServiceInversionCorrespondence.v) | Statement correspondence for `analysis/facts/busy_interval/service_inversion.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
