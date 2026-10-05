# `analysis/facts/suspension.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `suspended_implies_job_not_ready` | Lemma | `Prosa.Analysis.Facts.Suspension.suspended_implies_job_not_ready` | `suspended_implies_job_not_ready_correspondence` | [view](3_printed_declarations/suspended_implies_job_not_ready.md) |
| `suspended_implies_not_scheduled` | Lemma | `Prosa.Analysis.Facts.Suspension.suspended_implies_not_scheduled` | `suspended_implies_not_scheduled_correspondence` | [view](3_printed_declarations/suspended_implies_not_scheduled.md) |
| `suspended_implies_arrived` | Lemma | `Prosa.Analysis.Facts.Suspension.suspended_implies_arrived` | `suspended_implies_arrived_correspondence` | [view](3_printed_declarations/suspended_implies_arrived.md) |
| `suspended_implies_pending` | Lemma | `Prosa.Analysis.Facts.Suspension.suspended_implies_pending` | `suspended_implies_pending_correspondence` | [view](3_printed_declarations/suspended_implies_pending.md) |
| `suspended_implies_not_backlogged` | Lemma | `Prosa.Analysis.Facts.Suspension.suspended_implies_not_backlogged` | `suspended_implies_not_backlogged_correspondence` | [view](3_printed_declarations/suspended_implies_not_backlogged.md) |
| `pending_and_not_suspended_implies_ready` | Lemma | `Prosa.Analysis.Facts.Suspension.pending_and_not_suspended_implies_ready` | `pending_and_not_suspended_implies_ready_correspondence` | [view](3_printed_declarations/pending_and_not_suspended_implies_ready.md) |
| `suspension_bounded_trivial` | Lemma | `Prosa.Analysis.Facts.Suspension.suspension_bounded_trivial` | `suspension_bounded_trivial_correspondence` | [view](3_printed_declarations/suspension_bounded_trivial.md) |
| `suspension_bounded_longer_interval` | Lemma | `Prosa.Analysis.Facts.Suspension.suspension_bounded_longer_interval` | `suspension_bounded_longer_interval_correspondence` | [view](3_printed_declarations/suspension_bounded_longer_interval.md) |
| `suspension_bounded_in_interval_aux` | Lemma | `Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval_aux` | `suspension_bounded_in_interval_aux_correspondence` | [view](3_printed_declarations/suspension_bounded_in_interval_aux.md) |
| `exists_some_point` | Lemma | `Prosa.Analysis.Facts.Suspension.exists_some_point` | `exists_some_point_correspondence` | [view](3_printed_declarations/exists_some_point.md) |
| `suspension_bounded_in_interval` | Lemma | `Prosa.Analysis.Facts.Suspension.suspension_bounded_in_interval` | `suspension_bounded_in_interval_correspondence` | [view](3_printed_declarations/suspension_bounded_in_interval.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsSuspensionCorrespondence`](4_correspondence/FactsSuspensionCorrespondence.v) | Statement certificates for `analysis/facts/suspension.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
