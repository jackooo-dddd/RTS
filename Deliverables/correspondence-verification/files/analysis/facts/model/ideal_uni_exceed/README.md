# `analysis/facts/model/ideal_uni_exceed.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `eps_is_unit_supply` | Lemma | `Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_unit_supply` | `facts_unit_supply_model_correspondence` | [view](3_printed_declarations/eps_is_unit_supply.md) |
| `scheduled_at_procstate` | Lemma | `Prosa.Analysis.Facts.Model.IdealUniExceed.scheduled_at_procstate` | `facts_scheduled_at_procstate_statement_correspondence` | [view](3_printed_declarations/scheduled_at_procstate.md) |
| `eps_is_uniproc` | Lemma | `Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_uniproc` | `facts_uniprocessor_model_correspondence` | [view](3_printed_declarations/eps_is_uniproc.md) |
| `eps_is_fully_consuming` | Lemma | `Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_fully_consuming` | `facts_fully_consuming_model_correspondence` | [view](3_printed_declarations/eps_is_fully_consuming.md) |
| `eps_is_unit_service` | Lemma | `Prosa.Analysis.Facts.Model.IdealUniExceed.eps_is_unit_service` | `facts_unit_service_model_correspondence` | [view](3_printed_declarations/eps_is_unit_service.md) |
| `is_exceedance_exec` | Definition | `Prosa.Analysis.Facts.Model.IdealUniExceed.is_exceedance_exec` | `facts_is_exceedance_exec_correspondence` | [view](3_printed_declarations/is_exceedance_exec.md) |
| `blackout_implies_exceedance_execution` | Lemma | `Prosa.Analysis.Facts.Model.IdealUniExceed.blackout_implies_exceedance_execution` | `facts_blackout_statement_correspondence` | [view](3_printed_declarations/blackout_implies_exceedance_execution.md) |

## Certificates

| Module | Role |
|---|---|
| [`IdealUniExceedFactsSourceComputation`](4_correspondence/IdealUniExceedFactsSourceComputation.v) | The source computation is derived from the official ProcessorState fields, not from any of this file's seven public theorem proofs. |
| [`IdealUniExceedFactsExactTypeGuards`](4_correspondence/IdealUniExceedFactsExactTypeGuards.v) | All seven guards elaborate the official source constant and the imported production Lean constant against an explicit expected type. |
| [`IdealUniExceedFactsStateCorrespondence`](4_correspondence/IdealUniExceedFactsStateCorrespondence.v) | The source inductive and the imported Lean inductive remain distinct. |
| [`IdealUniExceedFactsCorrespondence`](4_correspondence/IdealUniExceedFactsCorrespondence.v) | Every statement below refers to the official v0.6 source constant and the actual imported production Lean artifact. |
| [`IdealUniExceedFactsOperations`](4_correspondence/IdealUniExceedFactsOperations.v) | Operation correspondence for the actual compiled finite Unit core folds. |
| [`IdealUniExceedFactsBlackoutStatement`](4_correspondence/IdealUniExceedFactsBlackoutStatement.v) | Proves or defines `facts_target_supply_in`, `facts_target_blackout_state`, `facts_blackout_state_canonical` and 6 more. |
| [`IdealUniExceedFactsModelCorrespondence`](4_correspondence/IdealUniExceedFactsModelCorrespondence.v) | Proves or defines `facts_unit_supply_model_correspondence`, `facts_unit_service_model_correspondence`, `facts_uniprocessor_model_correspondence` and 1 more. |
| [`IdealUniExceedFactsScheduledStatement`](4_correspondence/IdealUniExceedFactsScheduledStatement.v) | Proves or defines `facts_iff_correspondence`, `facts_state_or_correspondence`, `facts_scheduled_statement_point` and 1 more. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `IueTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
