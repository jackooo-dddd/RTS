# `analysis/facts/busy_interval/arrival.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `busy_interval_prefix_job_arrival` | Fact | `Prosa.Analysis.Facts.BusyInterval.Arrival.busy_interval_prefix_job_arrival` | `busy_interval_prefix_job_arrival_correspondence` | [view](3_printed_declarations/busy_interval_prefix_job_arrival.md) |
| `busy_interval_job_arrival` | Fact | `Prosa.Analysis.Facts.BusyInterval.Arrival.busy_interval_job_arrival` | `busy_interval_job_arrival_correspondence` | [view](3_printed_declarations/busy_interval_job_arrival.md) |
| `busy_prefix_starts_when_hep_job_arrives` | Lemma | `Prosa.Analysis.Facts.BusyInterval.Arrival.busy_prefix_starts_when_hep_job_arrives` | `busy_prefix_starts_when_hep_job_arrives_correspondence` | [view](3_printed_declarations/busy_prefix_starts_when_hep_job_arrives.md) |

## Certificates

| Module | Role |
|---|---|
| [`BusyIntervalArrivalCorrespondence`](4_correspondence/BusyIntervalArrivalCorrespondence.v) | Statement correspondence for `analysis/facts/busy_interval/arrival.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
