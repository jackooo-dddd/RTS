# `results/optimality/edf.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `EDF_optimality` | Theorem | `Prosa.Results.Optimality.Edf.EDF_optimality` | `EDF_optimality_correspondence` | [view](3_printed_declarations/EDF_optimality.md) |
| `EDF_WC_optimality` | Theorem | `Prosa.Results.Optimality.Edf.EDF_WC_optimality` | `EDF_WC_optimality_correspondence` | [view](3_printed_declarations/EDF_WC_optimality.md) |
| `EDF_priority_compliant_WC_optimality` | Corollary | `Prosa.Results.Optimality.Edf.EDF_priority_compliant_WC_optimality` | `EDF_priority_compliant_WC_optimality_correspondence` | [view](3_printed_declarations/EDF_priority_compliant_WC_optimality.md) |
| `weak_EDF_optimality` | Theorem | `Prosa.Results.Optimality.Edf.weak_EDF_optimality` | `weak_EDF_optimality_correspondence` | [view](3_printed_declarations/weak_EDF_optimality.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsEdfOptCorrespondence`](4_correspondence/FactsEdfOptCorrespondence.v) | Helper-only copy of accepted certificates/analysis_facts_transform_edf_opt/FactsEdfOptCorrespondence.v: the imported module name differs and the statement correspondences (whose statements are not … |
| [`OptimalityEdfCorrespondence`](4_correspondence/OptimalityEdfCorrespondence.v) | Statement correspondences for `results/optimality/edf.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
