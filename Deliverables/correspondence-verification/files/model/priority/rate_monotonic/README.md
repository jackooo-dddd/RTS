# `model/priority/rate_monotonic.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `RM` | Instance | `Prosa.Model.Priority.RateMonotonic.RM` | `RM_correspondence` | [view](3_printed_declarations/RM.md) |
| `RM_is_reflexive` | Lemma | `Prosa.Model.Priority.RateMonotonic.RM_is_reflexive` | `RM_is_reflexive_correspondence` | [view](3_printed_declarations/RM_is_reflexive.md) |
| `RM_is_transitive` | Lemma | `Prosa.Model.Priority.RateMonotonic.RM_is_transitive` | `RM_is_transitive_correspondence` | [view](3_printed_declarations/RM_is_transitive.md) |
| `RM_is_total` | Lemma | `Prosa.Model.Priority.RateMonotonic.RM_is_total` | `RM_is_total_correspondence` | [view](3_printed_declarations/RM_is_total.md) |

## Certificates

| Module | Role |
|---|---|
| [`PriorityRateMonotonicCorrespondence`](4_correspondence/PriorityRateMonotonicCorrespondence.v) | Certificates for `model/priority/rate_monotonic.v`: the parameter class (`SporadicModel`) is related pointwise on Nat with two-way totals; the policy instance(s) are related as `PdFPRel` for related … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `HEq_inst1`, `PdTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
