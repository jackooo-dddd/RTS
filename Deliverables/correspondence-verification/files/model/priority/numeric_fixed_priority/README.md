# `model/priority/numeric_fixed_priority.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `TaskPriority` | Class | `Prosa.Model.Priority.NumericFixedPriority.TaskPriority` | `TaskPriority_source_total, TaskPriority_target_total` | [view](3_printed_declarations/TaskPriority.md) |
| `NFPA_is_reflexive` | Lemma | `Prosa.Model.Priority.NumericFixedPriority.NFPA_is_reflexive` | `NFPA_is_reflexive_correspondence` | [view](3_printed_declarations/NFPA_is_reflexive.md) |
| `NFPA_is_transitive` | Lemma | `Prosa.Model.Priority.NumericFixedPriority.NFPA_is_transitive` | `NFPA_is_transitive_correspondence` | [view](3_printed_declarations/NFPA_is_transitive.md) |
| `NFPA_is_total` | Lemma | `Prosa.Model.Priority.NumericFixedPriority.NFPA_is_total` | `NFPA_is_total_correspondence` | [view](3_printed_declarations/NFPA_is_total.md) |
| `NFPD_is_reflexive` | Lemma | `Prosa.Model.Priority.NumericFixedPriority.NFPD_is_reflexive` | `NFPD_is_reflexive_correspondence` | [view](3_printed_declarations/NFPD_is_reflexive.md) |
| `NFPD_is_transitive` | Lemma | `Prosa.Model.Priority.NumericFixedPriority.NFPD_is_transitive` | `NFPD_is_transitive_correspondence` | [view](3_printed_declarations/NFPD_is_transitive.md) |
| `NFPD_is_total` | Lemma | `Prosa.Model.Priority.NumericFixedPriority.NFPD_is_total` | `NFPD_is_total_correspondence` | [view](3_printed_declarations/NFPD_is_total.md) |

## Certificates

| Module | Role |
|---|---|
| [`PriorityNumericFixedPriorityCorrespondence`](4_correspondence/PriorityNumericFixedPriorityCorrespondence.v) | Certificates for `model/priority/numeric_fixed_priority.v`: the parameter class (`TaskPriority`) is related pointwise on Nat with two-way totals; the policy instance(s) are related as `PdFPRel` for … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `HEq_inst1`, `PdTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
