# `analysis/facts/readiness/backlogged.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `mem_backlogged_jobs` | Lemma | `Prosa.Analysis.Facts.Readiness.Backlogged.mem_backlogged_jobs` | `mem_backlogged_jobs_correspondence` | [view](3_printed_declarations/mem_backlogged_jobs.md) |
| `backlogged_job_arrives_in` | Lemma | `Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_job_arrives_in` | `backlogged_job_arrives_in_correspondence` | [view](3_printed_declarations/backlogged_job_arrives_in.md) |
| `backlogged_prefix_invariance` | Lemma | `Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_prefix_invariance` | `backlogged_prefix_invariance_correspondence` | [view](3_printed_declarations/backlogged_prefix_invariance.md) |
| `backlogged_prefix_invariance'` | Corollary | `Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_prefix_invariance'` | `backlogged_prefix_invariance'_correspondence` | [view](3_printed_declarations/backlogged_prefix_invariance'.md) |
| `backlogged_jobs_prefix_invariance` | Lemma | `Prosa.Analysis.Facts.Readiness.Backlogged.backlogged_jobs_prefix_invariance` | `backlogged_jobs_prefix_invariance_correspondence` | [view](3_printed_declarations/backlogged_jobs_prefix_invariance.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsBackloggedCorrespondence`](4_correspondence/FactsBackloggedCorrespondence.v) | Statement correspondences for `analysis/facts/readiness/backlogged.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
