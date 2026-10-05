# `results/transfer_schedulability/paper_model.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `JobPredecessors` | Class | `Prosa.Results.TransferSchedulability.PaperModel.JobPredecessors` | `JobPredecessors_source_total, JobPredecessors_target_total` | [view](3_printed_declarations/JobPredecessors.md) |
| `JobDelay` | Class | `Prosa.Results.TransferSchedulability.PaperModel.JobDelay` | `JobDelay_source_total, JobDelay_target_total` | [view](3_printed_declarations/JobDelay.md) |
| `SystemEvolutions` | Class | `Prosa.Results.TransferSchedulability.PaperModel.SystemEvolutions` | `SystemEvolutions_source_total, SystemEvolutions_target_total` | [view](3_printed_declarations/SystemEvolutions.md) |
| `Scheduler` | Definition | `Prosa.Results.TransferSchedulability.PaperModel.Scheduler` | `Scheduler_source_total, Scheduler_target_total, Scheduler_generic_source_total, Scheduler_generic_target_total` | [view](3_printed_declarations/Scheduler.md) |
| `schedulability_transferred_AB` | Definition | `Prosa.Results.TransferSchedulability.PaperModel.schedulability_transferred_AB` | `schedulability_transferred_AB_correspondence` | [view](3_printed_declarations/schedulability_transferred_AB.md) |
| `clairvoyant_criterion` | Definition | `Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_criterion` | `clairvoyant_criterion_correspondence` | [view](3_printed_declarations/clairvoyant_criterion.md) |
| `clairvoyant_sufficiency` | Theorem | `Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_sufficiency` | `clairvoyant_sufficiency_correspondence` | [view](3_printed_declarations/clairvoyant_sufficiency.md) |
| `clairvoyant_necessity` | Theorem | `Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_necessity` | `clairvoyant_necessity_correspondence` | [view](3_printed_declarations/clairvoyant_necessity.md) |
| `nonclairvoyant_criterion` | Definition | `Prosa.Results.TransferSchedulability.PaperModel.nonclairvoyant_criterion` | `nonclairvoyant_criterion_correspondence` | [view](3_printed_declarations/nonclairvoyant_criterion.md) |
| `nonclairvoyant_sufficiency` | Theorem | `Prosa.Results.TransferSchedulability.PaperModel.nonclairvoyant_sufficiency` | `nonclairvoyant_sufficiency_correspondence` | [view](3_printed_declarations/nonclairvoyant_sufficiency.md) |
| `ref_finish_time` | Definition | `Prosa.Results.TransferSchedulability.PaperModel.ref_finish_time` | `ref_finish_time_correspondence` | [view](3_printed_declarations/ref_finish_time.md) |
| `online_response_time_bound` | Lemma | `Prosa.Results.TransferSchedulability.PaperModel.online_response_time_bound` | `online_response_time_bound_correspondence` | [view](3_printed_declarations/online_response_time_bound.md) |
| `online_finish_time` | Definition | `Prosa.Results.TransferSchedulability.PaperModel.online_finish_time` | `online_finish_time_correspondence` | [view](3_printed_declarations/online_finish_time.md) |
| `online_finish_time_bounded` | Definition | `Prosa.Results.TransferSchedulability.PaperModel.online_finish_time_bounded` | `online_finish_time_bounded_correspondence` | [view](3_printed_declarations/online_finish_time_bounded.md) |
| `clairvoyant_sufficiency'` | Theorem | `Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_sufficiency'` | `clairvoyant_sufficiency'_correspondence` | [view](3_printed_declarations/clairvoyant_sufficiency'.md) |
| `nonclairvoyant_sufficiency'` | Theorem | `Prosa.Results.TransferSchedulability.PaperModel.nonclairvoyant_sufficiency'` | `nonclairvoyant_sufficiency'_correspondence` | [view](3_printed_declarations/nonclairvoyant_sufficiency'.md) |
| `online_finish_time'` | Definition | `Prosa.Results.TransferSchedulability.PaperModel.online_finish_time'` | `online_finish_time'_correspondence` | [view](3_printed_declarations/online_finish_time'.md) |
| `online_finish_time_bounded'` | Definition | `Prosa.Results.TransferSchedulability.PaperModel.online_finish_time_bounded'` | `online_finish_time_bounded'_correspondence` | [view](3_printed_declarations/online_finish_time_bounded'.md) |
| `clairvoyant_necessity'` | Theorem | `Prosa.Results.TransferSchedulability.PaperModel.clairvoyant_necessity'` | `clairvoyant_necessity'_correspondence` | [view](3_printed_declarations/clairvoyant_necessity'.md) |

## Certificates

| Module | Role |
|---|---|
| [`PmArrivalsSeqBaseAdapter`](4_correspondence/PmArrivalsSeqBaseAdapter.v) | Proves or defines `ar_false_elim`, `ar_false_to_strict`, `ar_coq_false_to_target` and 23 more. |
| [`PmArrivalsSeqOperations`](4_correspondence/PmArrivalsSeqOperations.v) | Minimal operation-level correspondence layer for the actual compiled Arrival Sequence artifact. |
| [`PmArrivalsSeqCorrespondence`](4_correspondence/PmArrivalsSeqCorrespondence.v) | Fourteen compositional certificates for the official v0.6 definitions and the actual imported production Lean bodies. |
| [`PmJitterSvcNatBoolOperations`](4_correspondence/PmJitterSvcNatBoolOperations.v) | Artifact-local Nat and Bool operations used by the compiled Service definitions. |
| [`PmJitterSvcScheduleOperations`](4_correspondence/PmJitterSvcScheduleOperations.v) | Artifact-local instantiation of the already-certified ProcessorState observational relation. |
| [`PmJitterSvcJobOperations`](4_correspondence/PmJitterSvcJobOperations.v) | Full one-field class correspondence for the Job observations used by Service. |
| [`PmCriterionDefs`](4_correspondence/PmCriterionDefs.v) | The helper part and the definition certificates (lines 1-792, up to `End Definitions.`) of the accepted certificates/results_transfer_schedulability_criterion/CriterionCorrespondence.v, re-bound to … |
| [`PaperModelCorrespondence`](4_correspondence/PaperModelCorrespondence.v) | Correspondences for `results/transfer_schedulability/paper_model.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
