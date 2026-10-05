# `implementation/facts/extrapolated_arrival_curve.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `ltn_steps_is_transitive` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.ltn_steps_is_transitive` | `facts_ltn_steps_is_transitive_certificate` | [view](3_printed_declarations/ltn_steps_is_transitive.md) |
| `leq_steps_is_reflexive` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.leq_steps_is_reflexive` | `facts_leq_steps_is_reflexive_certificate` | [view](3_printed_declarations/leq_steps_is_reflexive.md) |
| `leq_steps_is_transitive` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.leq_steps_is_transitive` | `facts_leq_steps_is_transitive_certificate` | [view](3_printed_declarations/leq_steps_is_transitive.md) |
| `value_at_monotone` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.value_at_monotone` | `facts_value_at_monotone_certificate` | [view](3_printed_declarations/value_at_monotone.md) |
| `value_at_change_is_in_steps_of` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.value_at_change_is_in_steps_of` | `facts_value_at_change_is_in_steps_of_certificate` | [view](3_printed_declarations/value_at_change_is_in_steps_of.md) |
| `sorted_ltn_steps_imply_sorted_leq_steps_steps` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.sorted_ltn_steps_imply_sorted_leq_steps_steps` | `facts_sorted_ltn_implies_sorted_leq_certificate` | [view](3_printed_declarations/sorted_ltn_steps_imply_sorted_leq_steps_steps.md) |
| `step_at_0_is_00` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.step_at_0_is_00` | `facts_step_at_zero_certificate` | [view](3_printed_declarations/step_at_0_is_00.md) |
| `step_at_agrees_with_steps_of` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.step_at_agrees_with_steps_of` | `facts_step_at_agrees_with_steps_of_certificate` | [view](3_printed_declarations/step_at_agrees_with_steps_of.md) |
| `extrapolated_arrival_curve_is_monotone` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.extrapolated_arrival_curve_is_monotone` | `facts_extrapolated_arrival_curve_is_monotone_certificate` | [view](3_printed_declarations/extrapolated_arrival_curve_is_monotone.md) |
| `extrapolated_arrival_curve_change` | Lemma | `Prosa.Implementation.Facts.ExtrapolatedArrivalCurve.extrapolated_arrival_curve_change` | `facts_extrapolated_arrival_curve_change_certificate` | [view](3_printed_declarations/extrapolated_arrival_curve_change.md) |

## Certificates

| Module | Role |
|---|---|
| [`ExtrapolatedArrivalCurveFactsCorrespondence`](4_correspondence/ExtrapolatedArrivalCurveFactsCorrespondence.v) | These source declarations are signatures extracted from the pinned post-Section Rocq types. |
| [`ExtrapolatedArrivalCurveFactsExactTypeGuards`](4_correspondence/ExtrapolatedArrivalCurveFactsExactTypeGuards.v) | These guards are separate from the semantic certificates. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
