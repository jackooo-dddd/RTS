# `analysis/facts/model/preemption.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `preemption_time_interval_case` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.preemption_time_interval_case` | `preemption_time_interval_case_correspondence` | [view](3_printed_declarations/preemption_time_interval_case.md) |
| `idle_time_is_pt` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.idle_time_is_pt` | `idle_time_is_pt_correspondence` | [view](3_printed_declarations/idle_time_is_pt.md) |
| `zero_is_pt` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.zero_is_pt` | `zero_is_pt_correspondence` | [view](3_printed_declarations/zero_is_pt.md) |
| `first_moment_is_pt` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.first_moment_is_pt` | `first_moment_is_pt_correspondence` | [view](3_printed_declarations/first_moment_is_pt.md) |
| `neg_pt_scheduled_at` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.neg_pt_scheduled_at` | `neg_pt_scheduled_at_correspondence` | [view](3_printed_declarations/neg_pt_scheduled_at.md) |
| `neg_pt_scheduled_before` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.neg_pt_scheduled_before` | `neg_pt_scheduled_before_correspondence` | [view](3_printed_declarations/neg_pt_scheduled_before.md) |
| `neg_pt_scheduled_continuously_before` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.neg_pt_scheduled_continuously_before` | `neg_pt_scheduled_continuously_before_correspondence` | [view](3_printed_declarations/neg_pt_scheduled_continuously_before.md) |
| `neg_pt_scheduled_continuously_after` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.neg_pt_scheduled_continuously_after` | `neg_pt_scheduled_continuously_after_correspondence` | [view](3_printed_declarations/neg_pt_scheduled_continuously_after.md) |
| `neg_pt_scheduled_continuous` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.neg_pt_scheduled_continuous` | `neg_pt_scheduled_continuous_correspondence` | [view](3_printed_declarations/neg_pt_scheduled_continuous.md) |
| `neq_scheduled_at_pt` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.neq_scheduled_at_pt` | `neq_scheduled_at_pt_correspondence` | [view](3_printed_declarations/neq_scheduled_at_pt.md) |
| `neq_scheduled_at_pt_continuous_sched` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.neq_scheduled_at_pt_continuous_sched` | `neq_scheduled_at_pt_continuous_sched_correspondence` | [view](3_printed_declarations/neq_scheduled_at_pt_continuous_sched.md) |
| `scheduling_of_any_segment_starts_with_preemption_time` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.scheduling_of_any_segment_starts_with_preemption_time` | `scheduling_of_any_segment_starts_with_preemption_time_correspondence` | [view](3_printed_declarations/scheduling_of_any_segment_starts_with_preemption_time.md) |
| `scheduling_of_any_segment_starts_with_preemption_time_continuously_sched` | Lemma | `Prosa.Analysis.Facts.Model.Preemption.scheduling_of_any_segment_starts_with_preemption_time_continuously_sched` | `scheduling_of_any_segment_starts_with_preemption_time_continuously_sched_correspondence` | [view](3_printed_declarations/scheduling_of_any_segment_starts_with_preemption_time_continuously_sched.md) |
| `priority_higher_than_pending_job_priority` | Corollary | `Prosa.Analysis.Facts.Model.Preemption.priority_higher_than_pending_job_priority` | `priority_higher_than_pending_job_priority_correspondence` | [view](3_printed_declarations/priority_higher_than_pending_job_priority.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPreemptionCorrespondence`](4_correspondence/FactsPreemptionCorrespondence.v) | Statement correspondences for `analysis/facts/model/preemption.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
