# `analysis/definitions/finish_time.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `finish_time` | Definition | `Prosa.Analysis.Definitions.FinishTime.finish_time` | `finish_time_correspondence` | [view](3_printed_declarations/finish_time.md) |
| `finished_at_finish_time` | Corollary | `…FinishTime.finished_at_finish_time` | `finished_at_finish_time_statement_correspondence` | [view](3_printed_declarations/finished_at_finish_time.md) |
| `earliest_finish_time` | Corollary | `…FinishTime.earliest_finish_time` | `earliest_finish_time_statement_correspondence` | [view](3_printed_declarations/earliest_finish_time.md) |
| `completes_at_finish_time` | Corollary | `…FinishTime.completes_at_finish_time` | `completes_at_finish_time_statement_correspondence` | [view](3_printed_declarations/completes_at_finish_time.md) |
| `response_time` | Definition | `…FinishTime.response_time` | `response_time_correspondence` | [view](3_printed_declarations/response_time.md) |

## Certificates

| Module | Role |
|---|---|
| [`FinishTimeExactTypeGuards`](4_correspondence/FinishTimeExactTypeGuards.v) | Type guards on the source and imported constants. No certificate imports this module. |
| [`FinishTimeMinBridge`](4_correspondence/FinishTimeMinBridge.v) | MathComp `ex_minn` ↔ Lean `Nat.find` |
| [`FinishTimeCorrespondence`](4_correspondence/FinishTimeCorrespondence.v) | The five declaration certificates |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext`, `Quot_sound`, `Classical_choice` |
| Definitional UIP | `eq`, `eq_inst1`, `True`, `HEq`, `HEq_inst1`, `SvcTrue`, `SubNatTrue` |
| Rocq primitives | `PrimInt63.*` |
