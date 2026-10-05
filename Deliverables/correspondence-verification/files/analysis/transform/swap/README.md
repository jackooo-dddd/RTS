# `analysis/transform/swap.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `replace_at` | Definition | `Prosa.Analysis.Transform.Swap.replace_at` | `replace_at_correspondence` | [view](3_printed_declarations/replace_at.md) |
| `swapped` | Definition | `Prosa.Analysis.Transform.Swap.swapped` | `swapped_correspondence` | [view](3_printed_declarations/swapped.md) |

## Certificates

| Module | Role |
|---|---|
| [`SwapExactTypeGuards`](4_correspondence/SwapExactTypeGuards.v) | No description in the module. |
| [`SwapNatEquality`](4_correspondence/SwapNatEquality.v) | Proves or defines `swap_coq_false_to_target`, `swap_decidable_eq`, `swap_bool_to_rocq` and 3 more. |
| [`SwapCorrespondence`](4_correspondence/SwapCorrespondence.v) | The state representation is two-sided. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
