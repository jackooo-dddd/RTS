# `implementation/refinements/arrival_curve_prefix.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `has_valid_arrival_curve_prefix_tsk` | Lemma | `Prosa.Implementation.Refinements.ArrivalCurvePrefix.has_valid_arrival_curve_prefix_tsk` | `has_valid_arrival_curve_prefix_tsk_correspondence` | [view](3_printed_declarations/has_valid_arrival_curve_prefix_tsk.md) |
| `steps_are_positive_if_first_step_is_positive` | Lemma | `Prosa.Implementation.Refinements.ArrivalCurvePrefix.steps_are_positive_if_first_step_is_positive` | `steps_are_positive_if_first_step_is_positive_correspondence` | [view](3_printed_declarations/steps_are_positive_if_first_step_is_positive.md) |
| `nonshifted_offsets_are_positive` | Lemma | `Prosa.Implementation.Refinements.ArrivalCurvePrefix.nonshifted_offsets_are_positive` | `nonshifted_offsets_are_positive_correspondence` | [view](3_printed_declarations/nonshifted_offsets_are_positive.md) |
| `time_steps_sorted` | Lemma | `Prosa.Implementation.Refinements.ArrivalCurvePrefix.time_steps_sorted` | `time_steps_sorted_correspondence` | [view](3_printed_declarations/time_steps_sorted.md) |

## Certificates

| Module | Role |
|---|---|
| [`RacpBase`](4_correspondence/RacpBase.v) | Correspondences for `implementation/refinements/refinements.v`. |
| [`RefArrivalCurvePrefixCorrespondence`](4_correspondence/RefArrivalCurvePrefixCorrespondence.v) | Correspondences for `implementation/refinements/arrival_curve_prefix.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
