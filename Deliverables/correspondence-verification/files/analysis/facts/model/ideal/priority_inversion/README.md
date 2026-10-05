# `analysis/facts/model/ideal/priority_inversion.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `idle_implies_no_priority_inversion` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.PriorityInversion.idle_implies_no_priority_inversion` | `idle_implies_no_priority_inversion_correspondence` | [view](3_printed_declarations/idle_implies_no_priority_inversion.md) |
| `priority_inversion_equiv_sched_lower_priority` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.PriorityInversion.priority_inversion_equiv_sched_lower_priority` | `priority_inversion_equiv_sched_lower_priority_correspondence` | [view](3_printed_declarations/priority_inversion_equiv_sched_lower_priority.md) |
| `sched_hep_implies_no_priority_inversion` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.PriorityInversion.sched_hep_implies_no_priority_inversion` | `sched_hep_implies_no_priority_inversion_correspondence` | [view](3_printed_declarations/sched_hep_implies_no_priority_inversion.md) |
| `sched_lp_implies_priority_inversion` | Lemma | `Prosa.Analysis.Facts.Model.Ideal.PriorityInversion.sched_lp_implies_priority_inversion` | `sched_lp_implies_priority_inversion_correspondence` | [view](3_printed_declarations/sched_lp_implies_priority_inversion.md) |

## Certificates

| Module | Role |
|---|---|
| [`IdealPriorityInversionCorrespondence`](4_correspondence/IdealPriorityInversionCorrespondence.v) | Statement correspondences for `analysis/facts/model/ideal/priority_inversion.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
