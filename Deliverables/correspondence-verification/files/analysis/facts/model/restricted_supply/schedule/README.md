# `analysis/facts/model/restricted_supply/schedule.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `rs_proc_model_is_a_uniprocessor_model` | Lemma | `Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule.rs_proc_model_is_a_uniprocessor_model` | `facts_uniprocessor_model_correspondence` | [view](3_printed_declarations/rs_proc_model_is_a_uniprocessor_model.md) |
| `rs_proc_is_unit_supply` | Lemma | `Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule.rs_proc_is_unit_supply` | `facts_unit_supply_model_correspondence` | [view](3_printed_declarations/rs_proc_is_unit_supply.md) |
| `rs_proc_model_fully_consuming` | Lemma | `Prosa.Analysis.Facts.Model.RestrictedSupply.Schedule.rs_proc_model_fully_consuming` | `facts_fully_consuming_model_correspondence` | [view](3_printed_declarations/rs_proc_model_fully_consuming.md) |

## Certificates

| Module | Role |
|---|---|
| [`RestrictedSupplyScheduleBaseAdapter`](4_correspondence/RestrictedSupplyScheduleBaseAdapter.v) | Artifact-local Boolean and decidable-equality adapters, checked against the exact imported production module. |
| [`RestrictedSupplyScheduleSourceComputation`](4_correspondence/RestrictedSupplyScheduleSourceComputation.v) | These computations use the official source processor fields, not any of the three target source theorem proofs. |
| [`RestrictedSupplyScheduleExactTypeGuards`](4_correspondence/RestrictedSupplyScheduleExactTypeGuards.v) | All three source constants and all three imported production constants elaborate at their exact predicate types, without proxy statements. |
| [`RestrictedSupplyScheduleOperations`](4_correspondence/RestrictedSupplyScheduleOperations.v) | Operation correspondence for the actual compiled finite Unit core folds. |
| [`RestrictedSupplyScheduleModelCorrespondence`](4_correspondence/RestrictedSupplyScheduleModelCorrespondence.v) | Proves or defines `facts_unit_supply_model_correspondence`, `facts_uniprocessor_model_correspondence`, `facts_fully_consuming_model_correspondence`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `RssTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
