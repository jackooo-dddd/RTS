# `analysis/abstract/restricted_supply/iw_readiness.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `cumulative_interference_split` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.cumulative_interference_split` | `cumulative_interference_split_correspondence` | [view](3_printed_declarations/cumulative_interference_split.md) |
| `cumulative_interfering_workload_split` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.cumulative_interfering_workload_split` | `cumulative_interfering_workload_split_correspondence` | [view](3_printed_declarations/cumulative_interfering_workload_split.md) |
| `cumulative_task_interference_split` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.cumulative_task_interference_split` | `cumulative_task_interference_split_correspondence` | [view](3_printed_declarations/cumulative_task_interference_split.md) |
| `cumulative_intra_interference_split` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.cumulative_intra_interference_split` | `cumulative_intra_interference_split_correspondence` | [view](3_printed_declarations/cumulative_intra_interference_split.md) |
| `cumulative_iw_hep_eq_workload_of_ohep` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.cumulative_iw_hep_eq_workload_of_ohep` | `cumulative_iw_hep_eq_workload_of_ohep_correspondence` | [view](3_printed_declarations/cumulative_iw_hep_eq_workload_of_ohep.md) |
| `quiet_time_cl_implies_quiet_time_ab` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.quiet_time_cl_implies_quiet_time_ab` | `quiet_time_cl_implies_quiet_time_ab_correspondence` | [view](3_printed_declarations/quiet_time_cl_implies_quiet_time_ab.md) |
| `quiet_time_ab_implies_quiet_time_cl` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.quiet_time_ab_implies_quiet_time_cl` | `quiet_time_ab_implies_quiet_time_cl_correspondence` | [view](3_printed_declarations/quiet_time_ab_implies_quiet_time_cl.md) |
| `instantiated_quiet_time_equivalent_quiet_time` | Corollary | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.instantiated_quiet_time_equivalent_quiet_time` | `instantiated_quiet_time_equivalent_quiet_time_correspondence` | [view](3_printed_declarations/instantiated_quiet_time_equivalent_quiet_time.md) |
| `instantiated_busy_interval_prefix_equivalent_busy_interval_prefix` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix` | `instantiated_busy_interval_prefix_equivalent_busy_interval_prefix_correspondence` | [view](3_printed_declarations/instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.md) |
| `instantiated_busy_interval_equivalent_busy_interval` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.instantiated_busy_interval_equivalent_busy_interval` | `instantiated_busy_interval_equivalent_busy_interval_correspondence` | [view](3_printed_declarations/instantiated_busy_interval_equivalent_busy_interval.md) |
| `abstract_busy_interval_classic_quiet_time` | Fact | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.abstract_busy_interval_classic_quiet_time` | `abstract_busy_interval_classic_quiet_time_correspondence` | [view](3_printed_declarations/abstract_busy_interval_classic_quiet_time.md) |
| `abstract_busy_interval_classic_busy_interval_prefix` | Fact | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.abstract_busy_interval_classic_busy_interval_prefix` | `abstract_busy_interval_classic_busy_interval_prefix_correspondence` | [view](3_printed_declarations/abstract_busy_interval_classic_busy_interval_prefix.md) |
| `pending_hep_job_exists_inside_busy_interval` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.pending_hep_job_exists_inside_busy_interval` | `pending_hep_job_exists_inside_busy_interval_correspondence` | [view](3_printed_declarations/pending_hep_job_exists_inside_busy_interval.md) |
| `not_interference_implies_scheduled` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.not_interference_implies_scheduled` | `not_interference_implies_scheduled_correspondence` | [view](3_printed_declarations/not_interference_implies_scheduled.md) |
| `scheduled_implies_no_interference` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.scheduled_implies_no_interference` | `scheduled_implies_no_interference_correspondence` | [view](3_printed_declarations/scheduled_implies_no_interference.md) |
| `instantiated_i_and_w_are_coherent_with_schedule` | Corollary | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.instantiated_i_and_w_are_coherent_with_schedule` | `instantiated_i_and_w_are_coherent_with_schedule_correspondence` | [view](3_printed_declarations/instantiated_i_and_w_are_coherent_with_schedule.md) |
| `instantiated_interference_and_workload_consistent_with_sequential_tasks` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.instantiated_interference_and_workload_consistent_with_sequential_tasks` | `instantiated_interference_and_workload_consistent_with_sequential_tasks_correspondence` | [view](3_printed_declarations/instantiated_interference_and_workload_consistent_with_sequential_tasks.md) |
| `instantiated_i_and_w_no_speculative_execution` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.instantiated_i_and_w_no_speculative_execution` | `instantiated_i_and_w_no_speculative_execution_correspondence` | [view](3_printed_declarations/instantiated_i_and_w_no_speculative_execution.md) |

## Certificates

| Module | Role |
|---|---|
| [`IwReadinessCorrespondence`](4_correspondence/IwReadinessCorrespondence.v) | Statement correspondences for `analysis/abstract/restricted_supply/iw_readiness.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
