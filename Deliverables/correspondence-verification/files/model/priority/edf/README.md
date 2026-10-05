# `model/priority/edf.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `EDF` | Instance | `Prosa.Model.Priority.Edf.EDF` | `EDF_correspondence` | [view](3_printed_declarations/EDF.md) |
| `EDF_is_reflexive` | Lemma | `Prosa.Model.Priority.Edf.EDF_is_reflexive` | `EDF_is_reflexive_correspondence` | [view](3_printed_declarations/EDF_is_reflexive.md) |
| `EDF_is_transitive` | Lemma | `Prosa.Model.Priority.Edf.EDF_is_transitive` | `EDF_is_transitive_correspondence` | [view](3_printed_declarations/EDF_is_transitive.md) |
| `EDF_is_total` | Lemma | `Prosa.Model.Priority.Edf.EDF_is_total` | `EDF_is_total_correspondence` | [view](3_printed_declarations/EDF_is_total.md) |

## Certificates

| Module | Role |
|---|---|
| [`PriorityEdfCorrespondence`](4_correspondence/PriorityEdfCorrespondence.v) | Certificates for `model/priority/edf.v`: the parameter class (`JobDeadline`) is related pointwise on Nat with two-way totals; the policy instance(s) are related as `PdJLFPRel` for related parameters; … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `HEq_inst1`, `PdTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
