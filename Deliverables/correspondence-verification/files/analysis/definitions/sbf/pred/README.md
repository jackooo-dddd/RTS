# `analysis/definitions/sbf/pred.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `pred_sbf_respected` | Definition | `Prosa.Analysis.Definitions.Sbf.Pred.pred_sbf_respected` | `pred_sbf_respected_correspondence` | [view](3_printed_declarations/pred_sbf_respected.md) |
| `valid_pred_sbf` | Definition | `Prosa.Analysis.Definitions.Sbf.Pred.valid_pred_sbf` | `pred_valid_pred_sbf_correspondence` | [view](3_printed_declarations/valid_pred_sbf.md) |
| `sbf_is_monotone` | Definition | `Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone` | `pred_sbf_is_monotone_correspondence` | [view](3_printed_declarations/sbf_is_monotone.md) |
| `unit_supply_bound_function` | Definition | `Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function` | `pred_unit_supply_bound_function_correspondence` | [view](3_printed_declarations/unit_supply_bound_function.md) |
| `sbf_bounded_by_duration` | Remark | `Prosa.Analysis.Definitions.Sbf.Pred.sbf_bounded_by_duration` | `pred_sbf_bounded_by_duration_statement_correspondence` | [view](3_printed_declarations/sbf_bounded_by_duration.md) |

## Certificates

| Module | Role |
|---|---|
| [`PredExactTypeGuards`](4_correspondence/PredExactTypeGuards.v) | Only this separate guard mentions the source and target theorem proof constants. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
