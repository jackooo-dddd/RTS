# `analysis/facts/edf_definitions.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `EDF_schedule_implies_respects_policy_at_preemption_point` | Lemma | `Prosa.Analysis.Facts.EdfDefinitions.EDF_schedule_implies_respects_policy_at_preemption_point` | `EDF_schedule_implies_respects_policy_at_preemption_point_correspondence` | [view](3_printed_declarations/EDF_schedule_implies_respects_policy_at_preemption_point.md) |
| `respects_policy_at_preemption_point_implies_EDF_schedule` | Lemma | `Prosa.Analysis.Facts.EdfDefinitions.respects_policy_at_preemption_point_implies_EDF_schedule` | `respects_policy_at_preemption_point_implies_EDF_schedule_correspondence` | [view](3_printed_declarations/respects_policy_at_preemption_point_implies_EDF_schedule.md) |
| `EDF_schedule_equiv` | Corollary | `Prosa.Analysis.Facts.EdfDefinitions.EDF_schedule_equiv` | `EDF_schedule_equiv_correspondence` | [view](3_printed_declarations/EDF_schedule_equiv.md) |

## Certificates

| Module | Role |
|---|---|
| [`EdfDefinitionsCorrespondence`](4_correspondence/EdfDefinitionsCorrespondence.v) | Statement correspondences for `analysis/facts/edf_definitions.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
