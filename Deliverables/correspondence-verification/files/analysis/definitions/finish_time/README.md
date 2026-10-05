# `analysis/definitions/finish_time.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `finish_time` | Definition | `Prosa.Analysis.Definitions.FinishTime.finish_time` | `finish_time_correspondence` | [view](3_printed_declarations/finish_time.md) |
| `finished_at_finish_time` | Corollary | `Prosa.Analysis.Definitions.FinishTime.finished_at_finish_time` | `finished_at_finish_time_statement_correspondence` | [view](3_printed_declarations/finished_at_finish_time.md) |
| `earliest_finish_time` | Corollary | `Prosa.Analysis.Definitions.FinishTime.earliest_finish_time` | `earliest_finish_time_statement_correspondence` | [view](3_printed_declarations/earliest_finish_time.md) |
| `completes_at_finish_time` | Corollary | `Prosa.Analysis.Definitions.FinishTime.completes_at_finish_time` | `completes_at_finish_time_statement_correspondence` | [view](3_printed_declarations/completes_at_finish_time.md) |
| `response_time` | Definition | `Prosa.Analysis.Definitions.FinishTime.response_time` | `response_time_correspondence` | [view](3_printed_declarations/response_time.md) |

## Certificates

| Module | Role |
|---|---|
| [`FinishTimeExactTypeGuards`](4_correspondence/FinishTimeExactTypeGuards.v) | These guards deliberately mention the source and imported theorem constants. |
| [`FinishTimeCorrespondence`](4_correspondence/FinishTimeCorrespondence.v) | The actual v0.6 `ex_minn` definition is related to the compiled Lean `Nat.find` body through the independently checked minimum bridge. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
