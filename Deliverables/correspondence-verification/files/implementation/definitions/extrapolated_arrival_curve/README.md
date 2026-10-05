# `implementation/definitions/extrapolated_arrival_curve.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `ArrivalCurvePrefix` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ArrivalCurvePrefix` | `eac_prefix_imported_roundtrip` | [view](3_printed_declarations/ArrivalCurvePrefix.md) |
| `inter_arrival_to_prefix` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.inter_arrival_to_prefix` | `eac_inter_arrival_to_prefix_correspondence` | [view](3_printed_declarations/inter_arrival_to_prefix.md) |
| `horizon_of` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.horizon_of` | `eac_horizon_of_correspondence` | [view](3_printed_declarations/horizon_of.md) |
| `steps_of` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.steps_of` | `eac_steps_of_correspondence` | [view](3_printed_declarations/steps_of.md) |
| `time_steps_of` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.time_steps_of` | `eac_time_steps_of_correspondence` | [view](3_printed_declarations/time_steps_of.md) |
| `step_at` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.step_at` | `eac_step_at_correspondence` | [view](3_printed_declarations/step_at.md) |
| `value_at` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.value_at` | `eac_value_at_correspondence` | [view](3_printed_declarations/value_at.md) |
| `extrapolated_arrival_curve` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.extrapolated_arrival_curve` | `eac_extrapolated_arrival_curve_correspondence` | [view](3_printed_declarations/extrapolated_arrival_curve.md) |
| `positive_horizon` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.positive_horizon` | `eac_positive_horizon_correspondence` | [view](3_printed_declarations/positive_horizon.md) |
| `large_horizon` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon` | `eac_large_horizon_correspondence` | [view](3_printed_declarations/large_horizon.md) |
| `large_horizon_dec` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon_dec` | `eac_large_horizon_dec_correspondence` | [view](3_printed_declarations/large_horizon_dec.md) |
| `large_horizon_P` | Lemma | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.large_horizon_P` | `eac_large_horizon_P_statement_correspondence` | [view](3_printed_declarations/large_horizon_P.md) |
| `no_inf_arrivals` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.no_inf_arrivals` | `eac_no_inf_arrivals_correspondence` | [view](3_printed_declarations/no_inf_arrivals.md) |
| `specified_bursts` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.specified_bursts` | `eac_specified_bursts_correspondence` | [view](3_printed_declarations/specified_bursts.md) |
| `ltn_steps` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.ltn_steps` | `eac_ltn_steps_correspondence` | [view](3_printed_declarations/ltn_steps.md) |
| `sorted_ltn_steps` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_ltn_steps` | `eac_sorted_ltn_steps_correspondence` | [view](3_printed_declarations/sorted_ltn_steps.md) |
| `valid_arrival_curve_prefix` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix` | `eac_valid_arrival_curve_prefix_correspondence` | [view](3_printed_declarations/valid_arrival_curve_prefix.md) |
| `valid_arrival_curve_prefix_dec` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix_dec` | `eac_valid_arrival_curve_prefix_dec_correspondence` | [view](3_printed_declarations/valid_arrival_curve_prefix_dec.md) |
| `valid_arrival_curve_prefix_P` | Lemma | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.valid_arrival_curve_prefix_P` | `eac_valid_arrival_curve_prefix_P_statement_correspondence` | [view](3_printed_declarations/valid_arrival_curve_prefix_P.md) |
| `leq_steps` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.leq_steps` | `eac_leq_steps_correspondence` | [view](3_printed_declarations/leq_steps.md) |
| `sorted_leq_steps` | Definition | `Prosa.Implementation.Definitions.ExtrapolatedArrivalCurve.sorted_leq_steps` | `eac_sorted_leq_steps_correspondence` | [view](3_printed_declarations/sorted_leq_steps.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
