# `analysis/definitions/sbf/plain.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `supply_bound_function_respected` | Definition | `Prosa.Analysis.Definitions.Sbf.Plain.supply_bound_function_respected` | `plain_supply_bound_function_respected_correspondence` | [view](3_printed_declarations/supply_bound_function_respected.md) |
| `valid_supply_bound_function` | Definition | `Prosa.Analysis.Definitions.Sbf.Plain.valid_supply_bound_function` | `plain_valid_supply_bound_function_correspondence` | [view](3_printed_declarations/valid_supply_bound_function.md) |
| `sbf_respected_simplified` | Remark | `Prosa.Analysis.Definitions.Sbf.Plain.sbf_respected_simplified` | `plain_sbf_respected_simplified_statement_correspondence` | [view](3_printed_declarations/sbf_respected_simplified.md) |

## Certificates

| Module | Role |
|---|---|
| [`PlainExactTypeGuards`](4_correspondence/PlainExactTypeGuards.v) | Deliberately separate from the semantic certificate: these guards check the official and compiled theorem constants against precisely the two statement types structurally related by … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
