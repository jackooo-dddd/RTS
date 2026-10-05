# `util/minmax.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `leq_bigmax_cond_seq` | Lemma | `Prosa.Util.Minmax.leq_bigmax_cond_seq` | `leq_bigmax_cond_seq_statement_certificate` | [view](3_printed_declarations/leq_bigmax_cond_seq.md) |
| `leq_bigmax_sup` | Corollary | `Prosa.Util.Minmax.leq_bigmax_sup` | `leq_bigmax_sup_statement_certificate` | [view](3_printed_declarations/leq_bigmax_sup.md) |
| `bigmax_leq_seqP` | Lemma | `Prosa.Util.Minmax.bigmax_leq_seqP` | `bigmax_leq_seqP_statement_certificate` | [view](3_printed_declarations/bigmax_leq_seqP.md) |
| `leq_big_max` | Lemma | `Prosa.Util.Minmax.leq_big_max` | `leq_big_max_statement_certificate` | [view](3_printed_declarations/leq_big_max.md) |
| `bigmax_ord_ltn_identity` | Lemma | `Prosa.Util.Minmax.bigmax_ord_ltn_identity` | `bigmax_ord_ltn_identity_statement_certificate` | [view](3_printed_declarations/bigmax_ord_ltn_identity.md) |
| `bigmax_ltn_ord` | Lemma | `Prosa.Util.Minmax.bigmax_ltn_ord` | `bigmax_ltn_ord_statement_certificate` | [view](3_printed_declarations/bigmax_ltn_ord.md) |
| `bigmax_pred` | Lemma | `Prosa.Util.Minmax.bigmax_pred` | `bigmax_pred_statement_certificate` | [view](3_printed_declarations/bigmax_pred.md) |
| `bigmax_witness` | Lemma | `Prosa.Util.Minmax.bigmax_witness` | `bigmax_witness_statement_certificate` | [view](3_printed_declarations/bigmax_witness.md) |
| `bigmax_witness_diff` | Lemma | `Prosa.Util.Minmax.bigmax_witness_diff` | `bigmax_witness_diff_statement_certificate` | [view](3_printed_declarations/bigmax_witness_diff.md) |
| `bigmax_subset` | Corollary | `Prosa.Util.Minmax.bigmax_subset` | `bigmax_subset_statement_certificate` | [view](3_printed_declarations/bigmax_subset.md) |

## Certificates

| Module | Role |
|---|---|
| [`MinmaxCertificate`](4_correspondence/MinmaxCertificate.v) | Reusable logical composition for the Minmax artifact. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `HEq_inst1`, `MmTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
