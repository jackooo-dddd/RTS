# `implementation/facts/ideal_uni/preemption_aware.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `allocation_at_idle` | Lemma | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.allocation_at_idle` | `allocation_at_idle_correspondence` | [view](3_printed_declarations/allocation_at_idle.md) |
| `idle_schedule_no_backlogged_jobs` | Lemma | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.idle_schedule_no_backlogged_jobs` | `idle_schedule_no_backlogged_jobs_correspondence` | [view](3_printed_declarations/idle_schedule_no_backlogged_jobs.md) |
| `np_schedule_work_conserving` | Theorem | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_schedule_work_conserving` | `np_schedule_work_conserving_correspondence` | [view](3_printed_declarations/np_schedule_work_conserving.md) |
| `np_schedule_jobs_from_arrival_sequence` | Lemma | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_schedule_jobs_from_arrival_sequence` | `np_schedule_jobs_from_arrival_sequence_correspondence` | [view](3_printed_declarations/np_schedule_jobs_from_arrival_sequence.md) |
| `chosen_job_is_ready` | Theorem | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.chosen_job_is_ready` | `chosen_job_is_ready_correspondence` | [view](3_printed_declarations/chosen_job_is_ready.md) |
| `jobs_must_be_ready` | Theorem | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.jobs_must_be_ready` | `jobs_must_be_ready_correspondence` | [view](3_printed_declarations/jobs_must_be_ready.md) |
| `np_schedule_valid` | Theorem | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_schedule_valid` | `np_schedule_valid_correspondence` | [view](3_printed_declarations/np_schedule_valid.md) |
| `np_job_remains_scheduled` | Lemma | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_job_remains_scheduled` | `np_job_remains_scheduled_correspondence` | [view](3_printed_declarations/np_job_remains_scheduled.md) |
| `np_consistent` | Lemma | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_consistent` | `np_consistent_correspondence` | [view](3_printed_declarations/np_consistent.md) |
| `np_respects_preemption_model` | Lemma | `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_respects_preemption_model` | `np_respects_preemption_model_correspondence` | [view](3_printed_declarations/np_respects_preemption_model.md) |

## Certificates

| Module | Role |
|---|---|
| [`PreemptionAwareCorrespondence`](4_correspondence/PreemptionAwareCorrespondence.v) | Statement correspondences for `implementation/facts/ideal_uni/preemption_aware.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
