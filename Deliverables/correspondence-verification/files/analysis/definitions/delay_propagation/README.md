# `analysis/definitions/delay_propagation.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `valid_delay_propagation_mapping` | Definition | `Prosa.Analysis.Definitions.DelayPropagation.valid_delay_propagation_mapping` | `valid_delay_propagation_mapping_correspondence` | [view](3_printed_declarations/valid_delay_propagation_mapping.md) |
| `propagated_arrival_sequence` | Definition | `Prosa.Analysis.Definitions.DelayPropagation.propagated_arrival_sequence` | `propagated_arrival_sequence_correspondence` | [view](3_printed_declarations/propagated_arrival_sequence.md) |
| `job_mapping_uniq` | Definition | `Prosa.Analysis.Definitions.DelayPropagation.job_mapping_uniq` | `job_mapping_uniq_correspondence` | [view](3_printed_declarations/job_mapping_uniq.md) |
| `valid_arr_seq_propagation_mapping` | Definition | `Prosa.Analysis.Definitions.DelayPropagation.valid_arr_seq_propagation_mapping` | `valid_arr_seq_propagation_mapping_correspondence` | [view](3_printed_declarations/valid_arr_seq_propagation_mapping.md) |
| `jitter_delay_mapping_valid` | Remark | `Prosa.Analysis.Definitions.DelayPropagation.jitter_delay_mapping_valid` | `jitter_delay_mapping_valid_correspondence` | [view](3_printed_declarations/jitter_delay_mapping_valid.md) |
| `release_sequence` | Definition | `Prosa.Analysis.Definitions.DelayPropagation.release_sequence` | `release_sequence_correspondence` | [view](3_printed_declarations/release_sequence.md) |
| `jitter_arr_seq_mapping_valid` | Remark | `Prosa.Analysis.Definitions.DelayPropagation.jitter_arr_seq_mapping_valid` | `jitter_arr_seq_mapping_valid_correspondence` | [view](3_printed_declarations/jitter_arr_seq_mapping_valid.md) |

## Certificates

| Module | Role |
|---|---|
| [`DelayPropagationCorrespondence`](4_correspondence/DelayPropagationCorrespondence.v) | Correspondence certificates for `analysis/definitions/delay_propagation.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
