# `analysis/abstract/ideal/iw_instantiation.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `no_interference_when_idle` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.no_interference_when_idle` | `no_interference_when_idle_correspondence` | [view](3_printed_declarations/no_interference_when_idle.md) |
| `no_task_interference_when_idle` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.no_task_interference_when_idle` | `no_task_interference_when_idle_correspondence` | [view](3_printed_declarations/no_task_interference_when_idle.md) |
| `task_interference_eq_false` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.task_interference_eq_false` | `task_interference_eq_false_correspondence` | [view](3_printed_declarations/task_interference_eq_false.md) |
| `sched_athep_implies_task_interference` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.sched_athep_implies_task_interference` | `sched_athep_implies_task_interference_correspondence` | [view](3_printed_declarations/sched_athep_implies_task_interference.md) |
| `cumulative_interference_split` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.cumulative_interference_split` | `cumulative_interference_split_correspondence` | [view](3_printed_declarations/cumulative_interference_split.md) |
| `cumulative_interfering_workload_split` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.cumulative_interfering_workload_split` | `cumulative_interfering_workload_split_correspondence` | [view](3_printed_declarations/cumulative_interfering_workload_split.md) |
| `cumulative_task_interference_split` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.cumulative_task_interference_split` | `cumulative_task_interference_split_correspondence` | [view](3_printed_declarations/cumulative_task_interference_split.md) |
| `cumulative_iw_hep_eq_workload_of_ohep` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.cumulative_iw_hep_eq_workload_of_ohep` | `cumulative_iw_hep_eq_workload_of_ohep_correspondence` | [view](3_printed_declarations/cumulative_iw_hep_eq_workload_of_ohep.md) |
| `quiet_time_cl_implies_quiet_time_ab` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.quiet_time_cl_implies_quiet_time_ab` | `quiet_time_cl_implies_quiet_time_ab_correspondence` | [view](3_printed_declarations/quiet_time_cl_implies_quiet_time_ab.md) |
| `quiet_time_ab_implies_quiet_time_cl` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.quiet_time_ab_implies_quiet_time_cl` | `quiet_time_ab_implies_quiet_time_cl_correspondence` | [view](3_printed_declarations/quiet_time_ab_implies_quiet_time_cl.md) |
| `instantiated_quiet_time_equivalent_quiet_time` | Corollary | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_quiet_time_equivalent_quiet_time` | `instantiated_quiet_time_equivalent_quiet_time_correspondence` | [view](3_printed_declarations/instantiated_quiet_time_equivalent_quiet_time.md) |
| `instantiated_busy_interval_prefix_equivalent_busy_interval_prefix` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_busy_interval_prefix_equivalent_busy_interval_prefix` | `instantiated_busy_interval_prefix_equivalent_busy_interval_prefix_correspondence` | [view](3_printed_declarations/instantiated_busy_interval_prefix_equivalent_busy_interval_prefix.md) |
| `instantiated_busy_interval_equivalent_busy_interval` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_busy_interval_equivalent_busy_interval` | `instantiated_busy_interval_equivalent_busy_interval_correspondence` | [view](3_printed_declarations/instantiated_busy_interval_equivalent_busy_interval.md) |
| `abstract_busy_interval_classic_quiet_time` | Fact | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.abstract_busy_interval_classic_quiet_time` | `abstract_busy_interval_classic_quiet_time_correspondence` | [view](3_printed_declarations/abstract_busy_interval_classic_quiet_time.md) |
| `abstract_busy_interval_classic_busy_interval_prefix` | Fact | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.abstract_busy_interval_classic_busy_interval_prefix` | `abstract_busy_interval_classic_busy_interval_prefix_correspondence` | [view](3_printed_declarations/abstract_busy_interval_classic_busy_interval_prefix.md) |
| `not_interference_implies_scheduled` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.not_interference_implies_scheduled` | `not_interference_implies_scheduled_correspondence` | [view](3_printed_declarations/not_interference_implies_scheduled.md) |
| `scheduled_implies_no_interference` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.scheduled_implies_no_interference` | `scheduled_implies_no_interference_correspondence` | [view](3_printed_declarations/scheduled_implies_no_interference.md) |
| `instantiated_i_and_w_are_coherent_with_schedule` | Corollary | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_i_and_w_are_coherent_with_schedule` | `instantiated_i_and_w_are_coherent_with_schedule_correspondence` | [view](3_printed_declarations/instantiated_i_and_w_are_coherent_with_schedule.md) |
| `instantiated_interference_and_workload_consistent_with_sequential_tasks` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_interference_and_workload_consistent_with_sequential_tasks` | `instantiated_interference_and_workload_consistent_with_sequential_tasks_correspondence` | [view](3_printed_declarations/instantiated_interference_and_workload_consistent_with_sequential_tasks.md) |
| `instantiated_busy_intervals_are_bounded` | Lemma | `Prosa.Analysis.Abstract.Ideal.IwInstantiation.instantiated_busy_intervals_are_bounded` | `instantiated_busy_intervals_are_bounded_correspondence` | [view](3_printed_declarations/instantiated_busy_intervals_are_bounded.md) |

## Certificates

| Module | Role |
|---|---|
| [`IdealIwInstantiationCorrespondence`](4_correspondence/IdealIwInstantiationCorrespondence.v) | Main certificate: generated from the ideal-specific statement correspondences and the helper part of the accepted … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
