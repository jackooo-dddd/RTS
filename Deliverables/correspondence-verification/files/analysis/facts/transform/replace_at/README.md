# `analysis/facts/transform/replace_at.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `replace_at_def` | Lemma | `Prosa.Analysis.Facts.Transform.ReplaceAt.replace_at_def` | `replace_at_def_correspondence` | [view](3_printed_declarations/replace_at_def.md) |
| `rest_of_schedule_invariant` | Lemma | `Prosa.Analysis.Facts.Transform.ReplaceAt.rest_of_schedule_invariant` | `rest_of_schedule_invariant_correspondence` | [view](3_printed_declarations/rest_of_schedule_invariant.md) |
| `service_at_other_times_invariant` | Lemma | `Prosa.Analysis.Facts.Transform.ReplaceAt.service_at_other_times_invariant` | `service_at_other_times_invariant_correspondence` | [view](3_printed_declarations/service_at_other_times_invariant.md) |
| `service_delta` | Lemma | `Prosa.Analysis.Facts.Transform.ReplaceAt.service_delta` | `service_delta_correspondence` | [view](3_printed_declarations/service_delta.md) |
| `service_in_replaced` | Corollary | `Prosa.Analysis.Facts.Transform.ReplaceAt.service_in_replaced` | `service_in_replaced_correspondence` | [view](3_printed_declarations/service_in_replaced.md) |
| `service_at_of_others_invariant` | Lemma | `Prosa.Analysis.Facts.Transform.ReplaceAt.service_at_of_others_invariant` | `service_at_of_others_invariant_correspondence` | [view](3_printed_declarations/service_at_of_others_invariant.md) |
| `service_during_of_others_invariant` | Corollary | `Prosa.Analysis.Facts.Transform.ReplaceAt.service_during_of_others_invariant` | `service_during_of_others_invariant_correspondence` | [view](3_printed_declarations/service_during_of_others_invariant.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsReplaceAtCorrespondence`](4_correspondence/FactsReplaceAtCorrespondence.v) | Statement correspondences for `analysis/facts/transform/replace_at.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
