# `analysis/facts/model/sequential.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `scheduler_executes_job_with_earliest_arrival` | Corollary | `Prosa.Analysis.Facts.Model.Sequential.scheduler_executes_job_with_earliest_arrival` | `scheduler_executes_job_with_earliest_arrival_correspondence` | [view](3_printed_declarations/scheduler_executes_job_with_earliest_arrival.md) |
| `sequential_tasks_different_tasks` | Corollary | `Prosa.Analysis.Facts.Model.Sequential.sequential_tasks_different_tasks` | `sequential_tasks_different_tasks_correspondence` | [view](3_printed_declarations/sequential_tasks_different_tasks.md) |
| `sequential_tasks_from_readiness` | Lemma | `Prosa.Analysis.Facts.Model.Sequential.sequential_tasks_from_readiness` | `sequential_tasks_from_readiness_correspondence` | [view](3_printed_declarations/sequential_tasks_from_readiness.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsReadinessSequentialHelpers`](4_correspondence/FactsReadinessSequentialHelpers.v) | Helper copy (definition relations only) of the accepted statement correspondences for `analysis/facts/readiness/sequential.v`. |
| [`FactsModelSequentialCorrespondence`](4_correspondence/FactsModelSequentialCorrespondence.v) | Statement correspondences for `analysis/facts/model/sequential.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
