# `model/priority/deadline_monotonic.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `DM` | Instance | `Prosa.Model.Priority.DeadlineMonotonic.DM` | `DM_correspondence` | [view](3_printed_declarations/DM.md) |
| `DM_is_reflexive` | Lemma | `Prosa.Model.Priority.DeadlineMonotonic.DM_is_reflexive` | `DM_is_reflexive_correspondence` | [view](3_printed_declarations/DM_is_reflexive.md) |
| `DM_is_transitive` | Lemma | `Prosa.Model.Priority.DeadlineMonotonic.DM_is_transitive` | `DM_is_transitive_correspondence` | [view](3_printed_declarations/DM_is_transitive.md) |
| `DM_is_total` | Lemma | `Prosa.Model.Priority.DeadlineMonotonic.DM_is_total` | `DM_is_total_correspondence` | [view](3_printed_declarations/DM_is_total.md) |

## Certificates

| Module | Role |
|---|---|
| [`PriorityDeadlineMonotonicCorrespondence`](4_correspondence/PriorityDeadlineMonotonicCorrespondence.v) | Certificates for `model/priority/deadline_monotonic.v`: the parameter class (`TaskDeadline`) is related pointwise on Nat with two-way totals; the policy instance(s) are related as `PdFPRel` for … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `HEq_inst1`, `PdTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
