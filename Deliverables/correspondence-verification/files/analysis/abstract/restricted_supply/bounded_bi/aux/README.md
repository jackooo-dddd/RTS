# `analysis/abstract/restricted_supply/bounded_bi/aux.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `busy_interval_prefix_exists` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary.busy_interval_prefix_exists` | `busy_interval_prefix_exists_correspondence` | [view](3_printed_declarations/busy_interval_prefix_exists.md) |
| `service_lt_workload_in_busy` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary.service_lt_workload_in_busy` | `service_lt_workload_in_busy_correspondence` | [view](3_printed_declarations/service_lt_workload_in_busy.md) |
| `workload_exceeds_interval` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Auxiliary.workload_exceeds_interval` | `workload_exceeds_interval_correspondence` | [view](3_printed_declarations/workload_exceeds_interval.md) |

## Certificates

| Module | Role |
|---|---|
| [`BoundedBiAuxCorrespondence`](4_correspondence/BoundedBiAuxCorrespondence.v) | Statement correspondences for `analysis/abstract/restricted_supply/bounded_bi/aux.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
