# `analysis/facts/behavior/deadlines.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `incomplete_implies_later_deadline` | Lemma | `Prosa.Analysis.Facts.Behavior.Deadlines.incomplete_implies_later_deadline` | `incomplete_implies_later_deadline_correspondence` | [view](3_printed_declarations/incomplete_implies_later_deadline.md) |
| `incomplete_implies_scheduled_later` | Lemma | `Prosa.Analysis.Facts.Behavior.Deadlines.incomplete_implies_scheduled_later` | `incomplete_implies_scheduled_later_correspondence` | [view](3_printed_declarations/incomplete_implies_scheduled_later.md) |
| `scheduled_at_implies_later_deadline` | Lemma | `Prosa.Analysis.Facts.Behavior.Deadlines.scheduled_at_implies_later_deadline` | `scheduled_at_implies_later_deadline_correspondence` | [view](3_printed_declarations/scheduled_at_implies_later_deadline.md) |
| `service_invariant_implies_deadline_met` | Lemma | `Prosa.Analysis.Facts.Behavior.Deadlines.service_invariant_implies_deadline_met` | `service_invariant_implies_deadline_met_correspondence` | [view](3_printed_declarations/service_invariant_implies_deadline_met.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsDeadlinesCorrespondence`](4_correspondence/FactsDeadlinesCorrespondence.v) | Statement correspondences for `analysis/facts/behavior/deadlines.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
