# `implementation/facts/job_constructor.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_generation_valid_number` | Lemma | `Prosa.Implementation.Facts.JobConstructor.job_generation_valid_number` | `job_generation_valid_number_correspondence` | [view](3_printed_declarations/job_generation_valid_number.md) |
| `generate_jobs_at_unique` | Lemma | `Prosa.Implementation.Facts.JobConstructor.generate_jobs_at_unique` | `generate_jobs_at_unique_correspondence` | [view](3_printed_declarations/generate_jobs_at_unique.md) |
| `job_arrival_consistent` | Lemma | `Prosa.Implementation.Facts.JobConstructor.job_arrival_consistent` | `job_arrival_consistent_correspondence` | [view](3_printed_declarations/job_arrival_consistent.md) |
| `arrivals_at_unique` | Lemma | `Prosa.Implementation.Facts.JobConstructor.arrivals_at_unique` | `arrivals_at_unique_correspondence` | [view](3_printed_declarations/arrivals_at_unique.md) |
| `arrivals_between_unique` | Lemma | `Prosa.Implementation.Facts.JobConstructor.arrivals_between_unique` | `arrivals_between_unique_correspondence` | [view](3_printed_declarations/arrivals_between_unique.md) |
| `job_generation_valid_jobs` | Corollary | `Prosa.Implementation.Facts.JobConstructor.job_generation_valid_jobs` | `job_generation_valid_jobs_correspondence` | [view](3_printed_declarations/job_generation_valid_jobs.md) |

## Certificates

| Module | Role |
|---|---|
| [`JcJitterSvcNatBoolOperations`](4_correspondence/JcJitterSvcNatBoolOperations.v) | Replay of the accepted certificate module implementation_definitions_maximal_arrival_sequence/JitterSvcNatBoolOperations.v at this export: ImportedMaximalArrivalSequence is this export's … |
| [`JcMaximalArrivalSequenceCorrespondence`](4_correspondence/JcMaximalArrivalSequenceCorrespondence.v) | Replay of the accepted certificate module implementation_definitions_maximal_arrival_sequence/MaximalArrivalSequenceCorrespondence.v at this export: ImportedMaximalArrivalSequence is this export's … |
| [`FactsJobConstructorCorrespondence`](4_correspondence/FactsJobConstructorCorrespondence.v) | Statement correspondences for `implementation/facts/job_constructor.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
