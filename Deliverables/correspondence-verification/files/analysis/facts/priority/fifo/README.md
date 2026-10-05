# `analysis/facts/priority/fifo.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `hep_job_arrival_FIFO` | Fact | `Prosa.Analysis.Facts.Priority.Fifo.hep_job_arrival_FIFO` | `hep_job_arrival_FIFO_correspondence` | [view](3_printed_declarations/hep_job_arrival_FIFO.md) |
| `not_hep_job_arrival_FIFO` | Fact | `Prosa.Analysis.Facts.Priority.Fifo.not_hep_job_arrival_FIFO` | `not_hep_job_arrival_FIFO_correspondence` | [view](3_printed_declarations/not_hep_job_arrival_FIFO.md) |
| `not_hep_job_FIFO` | Fact | `Prosa.Analysis.Facts.Priority.Fifo.not_hep_job_FIFO` | `not_hep_job_FIFO_correspondence` | [view](3_printed_declarations/not_hep_job_FIFO.md) |
| `not_hep_job_always_higher_priority_FIFO` | Fact | `Prosa.Analysis.Facts.Priority.Fifo.not_hep_job_always_higher_priority_FIFO` | `not_hep_job_always_higher_priority_FIFO_correspondence` | [view](3_printed_declarations/not_hep_job_always_higher_priority_FIFO.md) |
| `FIFO_implies_no_priority_inversion` | Lemma | `Prosa.Analysis.Facts.Priority.Fifo.FIFO_implies_no_priority_inversion` | `FIFO_implies_no_priority_inversion_correspondence` | [view](3_printed_declarations/FIFO_implies_no_priority_inversion.md) |
| `scheduled_implies_higher_priority_completed` | Lemma | `Prosa.Analysis.Facts.Priority.Fifo.scheduled_implies_higher_priority_completed` | `scheduled_implies_higher_priority_completed_correspondence` | [view](3_printed_declarations/scheduled_implies_higher_priority_completed.md) |
| `FIFO_implies_no_pi` | Lemma | `Prosa.Analysis.Facts.Priority.Fifo.FIFO_implies_no_pi` | `FIFO_implies_no_pi_correspondence` | [view](3_printed_declarations/FIFO_implies_no_pi.md) |
| `FIFO_implies_no_service_inversion` | Corollary | `Prosa.Analysis.Facts.Priority.Fifo.FIFO_implies_no_service_inversion` | `FIFO_implies_no_service_inversion_correspondence` | [view](3_printed_declarations/FIFO_implies_no_service_inversion.md) |
| `tasks_execute_sequentially` | Lemma | `Prosa.Analysis.Facts.Priority.Fifo.tasks_execute_sequentially` | `tasks_execute_sequentially_correspondence` | [view](3_printed_declarations/tasks_execute_sequentially.md) |
| `fifo_respects_sequential_tasks` | Fact | `Prosa.Analysis.Facts.Priority.Fifo.fifo_respects_sequential_tasks` | `fifo_respects_sequential_tasks_correspondence` | [view](3_printed_declarations/fifo_respects_sequential_tasks.md) |
| `no_preemptions_under_FIFO` | Lemma | `Prosa.Analysis.Facts.Priority.Fifo.no_preemptions_under_FIFO` | `no_preemptions_under_FIFO_correspondence` | [view](3_printed_declarations/no_preemptions_under_FIFO.md) |
| `FIFO_is_nonpreemptive` | Corollary | `Prosa.Analysis.Facts.Priority.Fifo.FIFO_is_nonpreemptive` | `FIFO_is_nonpreemptive_correspondence` | [view](3_printed_declarations/FIFO_is_nonpreemptive.md) |

## Certificates

| Module | Role |
|---|---|
| [`BsiHelpers`](4_correspondence/BsiHelpers.v) | Helper-only copy of the accepted certificates/analysis_facts_busy_interval_service_inversion/ BusyIntervalServiceInversionCorrespondence.v (re-bound to this export), truncated after its helper … |
| [`FifoHelpers`](4_correspondence/FifoHelpers.v) | Helper-only copy of the accepted certificates/model_priority_fifo/PriorityFifoCorrespondence.v (re-bound to this export), truncated before its three statement correspondences (whose target statements … |
| [`FactsPriorityFifoCorrespondence`](4_correspondence/FactsPriorityFifoCorrespondence.v) | Statement correspondences for `analysis/facts/priority/fifo.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
