# `analysis/abstract/restricted_supply/task_ibf_readiness.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_intra_IBF` | Definition | `Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness.task_intra_IBF` | `task_intra_IBF_correspondence` | [view](3_printed_declarations/task_intra_IBF.md) |
| `instantiated_task_intra_interference_is_bounded` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.TaskIbfReadiness.instantiated_task_intra_interference_is_bounded` | `instantiated_task_intra_interference_is_bounded_correspondence` | [view](3_printed_declarations/instantiated_task_intra_interference_is_bounded.md) |

## Certificates

| Module | Role |
|---|---|
| [`IwReadinessCorrespondence`](4_correspondence/IwReadinessCorrespondence.v) | Helper-only copy of the accepted certificates/analysis_abstract_restricted_supply_iw_readiness/IwReadinessCorrespondence.v, re-bound to this export: the statement correspondences (whose statements … |
| [`TaskIbfReadinessCorrespondence`](4_correspondence/TaskIbfReadinessCorrespondence.v) | Definition and statement correspondences for `analysis/abstract/restricted_supply/task_ibf_readiness.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
