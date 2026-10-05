# `analysis/definitions/readiness.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `nonclairvoyant_readiness` | Definition | `Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness` | `nonclairvoyant_readiness_correspondence` | [view](3_printed_declarations/nonclairvoyant_readiness.md) |
| `valid_nonpreemptive_readiness` | Definition | `Prosa.Analysis.Definitions.Readiness.valid_nonpreemptive_readiness` | `valid_nonpreemptive_readiness_correspondence` | [view](3_printed_declarations/valid_nonpreemptive_readiness.md) |
| `sequential_readiness` | Definition | `Prosa.Analysis.Definitions.Readiness.sequential_readiness` | `sequential_readiness_correspondence` | [view](3_printed_declarations/sequential_readiness.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
