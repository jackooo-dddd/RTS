# `util/sum.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `sum_nat_eq0_nat` | Lemma | `Prosa.Util.Sum.sum_nat_eq0_nat` | `sum_nat_eq0_nat_statement_certificate` | [view](3_printed_declarations/sum_nat_eq0_nat.md) |
| `sum_nat_gt0` | Lemma | `Prosa.Util.Sum.sum_nat_gt0` | `sum_nat_gt0_statement_certificate` | [view](3_printed_declarations/sum_nat_gt0.md) |
| `sum_majorant_constant` | Lemma | `Prosa.Util.Sum.sum_majorant_constant` | `sum_majorant_constant_statement_certificate` | [view](3_printed_declarations/sum_majorant_constant.md) |
| `sum_split_exhaustive_mutually_exclusive_preds` | Lemma | `Prosa.Util.Sum.sum_split_exhaustive_mutually_exclusive_preds` | `sum_split_exhaustive_mutually_exclusive_preds_statement_certificate` | [view](3_printed_declarations/sum_split_exhaustive_mutually_exclusive_preds.md) |
| `bigmax_leq_sum` | Lemma | `Prosa.Util.Sum.bigmax_leq_sum` | `bigmax_leq_sum_statement_certificate` | [view](3_printed_declarations/bigmax_leq_sum.md) |
| `sum_le_subseq` | Lemma | `Prosa.Util.Sum.sum_le_subseq` | `sum_le_subseq_statement_certificate` | [view](3_printed_declarations/sum_le_subseq.md) |
| `leq_sum_seq` | Lemma | `Prosa.Util.Sum.leq_sum_seq` | `leq_sum_seq_statement_certificate` | [view](3_printed_declarations/leq_sum_seq.md) |
| `eq_sum_seq` | Lemma | `Prosa.Util.Sum.eq_sum_seq` | `eq_sum_seq_statement_certificate` | [view](3_printed_declarations/eq_sum_seq.md) |
| `leq_sum_seq_pred` | Lemma | `Prosa.Util.Sum.leq_sum_seq_pred` | `leq_sum_seq_pred_statement_certificate` | [view](3_printed_declarations/leq_sum_seq_pred.md) |
| `leq_sum_subseq` | Lemma | `Prosa.Util.Sum.leq_sum_subseq` | `leq_sum_subseq_statement_certificate` | [view](3_printed_declarations/leq_sum_subseq.md) |
| `leq_sum_sub_uniq` | Lemma | `Prosa.Util.Sum.leq_sum_sub_uniq` | `leq_sum_sub_uniq_statement_certificate` | [view](3_printed_declarations/leq_sum_sub_uniq.md) |
| `ltn_sum_leq_seq` | Lemma | `Prosa.Util.Sum.ltn_sum_leq_seq` | `ltn_sum_leq_seq_statement_certificate` | [view](3_printed_declarations/ltn_sum_leq_seq.md) |
| `eq_sum_leq_seq` | Lemma | `Prosa.Util.Sum.eq_sum_leq_seq` | `eq_sum_leq_seq_statement_certificate` | [view](3_printed_declarations/eq_sum_leq_seq.md) |
| `sum_of_ones` | Lemma | `Prosa.Util.Sum.sum_of_ones` | `sum_of_ones_statement_certificate` | [view](3_printed_declarations/sum_of_ones.md) |
| `big_nat_eq0` | Lemma | `Prosa.Util.Sum.big_nat_eq0` | `big_nat_eq0_statement_certificate` | [view](3_printed_declarations/big_nat_eq0.md) |
| `sum_le_summation_range` | Lemma | `Prosa.Util.Sum.sum_le_summation_range` | `sum_le_summation_range_statement_certificate` | [view](3_printed_declarations/sum_le_summation_range.md) |
| `big_sum_eq_in_eq_sized_intervals` | Lemma | `Prosa.Util.Sum.big_sum_eq_in_eq_sized_intervals` | `big_sum_eq_in_eq_sized_intervals_statement_certificate` | [view](3_printed_declarations/big_sum_eq_in_eq_sized_intervals.md) |
| `sum_over_partitions_le` | Lemma | `Prosa.Util.Sum.sum_over_partitions_le` | `sum_over_partitions_le_statement_certificate` | [view](3_printed_declarations/sum_over_partitions_le.md) |
| `reorder_summation` | Lemma | `Prosa.Util.Sum.reorder_summation` | `reorder_summation_statement_certificate` | [view](3_printed_declarations/reorder_summation.md) |
| `sum_over_partitions_eq` | Lemma | `Prosa.Util.Sum.sum_over_partitions_eq` | `sum_over_partitions_eq_statement_certificate` | [view](3_printed_declarations/sum_over_partitions_eq.md) |
| `sum_leq_mono` | Lemma | `Prosa.Util.Sum.sum_leq_mono` | `sum_leq_mono_statement_certificate` | [view](3_printed_declarations/sum_leq_mono.md) |
| `sum_unit1` | Lemma | `Prosa.Util.Sum.sum_unit1` | `sum_unit1_statement_certificate` | [view](3_printed_declarations/sum_unit1.md) |
| `pigeonhole_on_interval` | Lemma | `Prosa.Util.Sum.pigeonhole_on_interval` | `pigeonhole_on_interval_statement_certificate` | [view](3_printed_declarations/pigeonhole_on_interval.md) |
| `sum_ge_2_seq` | Lemma | `Prosa.Util.Sum.sum_ge_2_seq` | `sum_ge_2_seq_statement_certificate` | [view](3_printed_declarations/sum_ge_2_seq.md) |
| `sum_ge_2_nat` | Lemma | `Prosa.Util.Sum.sum_ge_2_nat` | `sum_ge_2_nat_statement_certificate` | [view](3_printed_declarations/sum_ge_2_nat.md) |

## Certificates

| Module | Role |
|---|---|
| [`SumIntervalCertificate`](4_correspondence/SumIntervalCertificate.v) | Definitional guards that bind the independently proved semantic shells to the exact automatically extracted source statement definitions. |
| [`SumSequenceCertificate`](4_correspondence/SumSequenceCertificate.v) | Exact structural target propositions at the approved `eqType -> carrier Type + canonical DecidableEq` boundary. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SsTruth`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
