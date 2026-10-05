# `analysis/facts/readiness/sequential.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `sequential_readiness_is_sequential` | Fact | `Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_is_sequential` | `sequential_readiness_is_sequential_correspondence` | [view](3_printed_declarations/sequential_readiness_is_sequential.md) |
| `sequential_readiness_nonclairvoyance` | Fact | `Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_nonclairvoyance` | `sequential_readiness_nonclairvoyance_correspondence` | [view](3_printed_declarations/sequential_readiness_nonclairvoyance.md) |
| `sequential_readiness_implies_sequential_tasks` | Lemma | `Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_implies_sequential_tasks` | `sequential_readiness_implies_sequential_tasks_correspondence` | [view](3_printed_declarations/sequential_readiness_implies_sequential_tasks.md) |
| `sequential_readiness_implies_work_bearing_readiness` | Lemma | `Prosa.Analysis.Facts.Readiness.Sequential.sequential_readiness_implies_work_bearing_readiness` | `sequential_readiness_implies_work_bearing_readiness_correspondence` | [view](3_printed_declarations/sequential_readiness_implies_work_bearing_readiness.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsReadinessSequentialCorrespondence`](4_correspondence/FactsReadinessSequentialCorrespondence.v) | Statement correspondences for `analysis/facts/readiness/sequential.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
