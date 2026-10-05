# `analysis/abstract/definitions.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `Interference` | Class | `Prosa.Analysis.Abstract.Definitions.Interference` | `ad_interference_import_certificate` | [view](3_printed_declarations/Interference.md) |
| `InterferingWorkload` | Class | `Prosa.Analysis.Abstract.Definitions.InterferingWorkload` | `ad_workload_import_certificate` | [view](3_printed_declarations/InterferingWorkload.md) |
| `cond_interference` | Definition | `Prosa.Analysis.Abstract.Definitions.cond_interference` | `cond_interference_correspondence` | [view](3_printed_declarations/cond_interference.md) |
| `cumul_cond_interference` | Definition | `Prosa.Analysis.Abstract.Definitions.cumul_cond_interference` | `cumul_cond_interference_correspondence` | [view](3_printed_declarations/cumul_cond_interference.md) |
| `cumulative_interference` | Definition | `Prosa.Analysis.Abstract.Definitions.cumulative_interference` | `cumulative_interference_correspondence` | [view](3_printed_declarations/cumulative_interference.md) |
| `cumulative_interfering_workload` | Definition | `Prosa.Analysis.Abstract.Definitions.cumulative_interfering_workload` | `cumulative_interfering_workload_correspondence` | [view](3_printed_declarations/cumulative_interfering_workload.md) |
| `no_speculative_execution` | Definition | `Prosa.Analysis.Abstract.Definitions.no_speculative_execution` | `no_speculative_execution_correspondence` | [view](3_printed_declarations/no_speculative_execution.md) |
| `quiet_time` | Definition | `Prosa.Analysis.Abstract.Definitions.quiet_time` | `ad_quiet_time_correspondence` | [view](3_printed_declarations/quiet_time.md) |
| `busy_interval_prefix` | Definition | `Prosa.Analysis.Abstract.Definitions.busy_interval_prefix` | `ad_busy_interval_prefix_correspondence` | [view](3_printed_declarations/busy_interval_prefix.md) |
| `busy_interval` | Definition | `Prosa.Analysis.Abstract.Definitions.busy_interval` | `ad_busy_interval_correspondence` | [view](3_printed_declarations/busy_interval.md) |
| `busy_interval_is_unique` | Fact | `Prosa.Analysis.Abstract.Definitions.busy_interval_is_unique` | `ad_busy_interval_unique_statement_correspondence` | [view](3_printed_declarations/busy_interval_is_unique.md) |
| `work_conserving` | Definition | `Prosa.Analysis.Abstract.Definitions.work_conserving` | `ad_work_conserving_correspondence` | [view](3_printed_declarations/work_conserving.md) |
| `busy_intervals_are_bounded_by` | Definition | `Prosa.Analysis.Abstract.Definitions.busy_intervals_are_bounded_by` | `ad_busy_intervals_bounded_correspondence` | [view](3_printed_declarations/busy_intervals_are_bounded_by.md) |
| `cond_interference_is_bounded_by` | Definition | `Prosa.Analysis.Abstract.Definitions.cond_interference_is_bounded_by` | `ad_cond_interference_bounded_correspondence` | [view](3_printed_declarations/cond_interference_is_bounded_by.md) |
| `job_interference_is_bounded_by` | Definition | `Prosa.Analysis.Abstract.Definitions.job_interference_is_bounded_by` | `ad_job_interference_bounded_correspondence` | [view](3_printed_declarations/job_interference_is_bounded_by.md) |

## Certificates

| Module | Role |
|---|---|
| [`AbstractDefinitionsJobBound`](4_correspondence/AbstractDefinitionsJobBound.v) | The unconditional bound is definitionally the conditional bound for the constant true predicate. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
