# `util/bigcat.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `mem_bigcat_nat` | Lemma | `Prosa.Util.Bigcat.mem_bigcat_nat` | `mem_bigcat_nat_statement_certificate` | [view](3_printed_declarations/mem_bigcat_nat.md) |
| `mem_bigcat_nat_exists` | Lemma | `Prosa.Util.Bigcat.mem_bigcat_nat_exists` | `mem_bigcat_nat_exists_statement_certificate` | [view](3_printed_declarations/mem_bigcat_nat_exists.md) |
| `mem_bigcat_ord` | Lemma | `Prosa.Util.Bigcat.mem_bigcat_ord` | `mem_bigcat_ord_statement_certificate` | [view](3_printed_declarations/mem_bigcat_ord.md) |
| `bigcat_nat_uniq` | Lemma | `Prosa.Util.Bigcat.bigcat_nat_uniq` | `bigcat_nat_uniq_statement_certificate` | [view](3_printed_declarations/bigcat_nat_uniq.md) |
| `bigcat_nat_filter_eq_filter_bigcat_nat` | Lemma | `Prosa.Util.Bigcat.bigcat_nat_filter_eq_filter_bigcat_nat` | `bigcat_nat_filter_eq_filter_bigcat_nat_statement_certificate` | [view](3_printed_declarations/bigcat_nat_filter_eq_filter_bigcat_nat.md) |
| `size_big_nat` | Lemma | `Prosa.Util.Bigcat.size_big_nat` | `size_big_nat_statement_certificate` | [view](3_printed_declarations/size_big_nat.md) |
| `mem_bigcat` | Lemma | `Prosa.Util.Bigcat.mem_bigcat` | `mem_bigcat_statement_certificate` | [view](3_printed_declarations/mem_bigcat.md) |
| `mem_bigcat_exists` | Lemma | `Prosa.Util.Bigcat.mem_bigcat_exists` | `mem_bigcat_exists_statement_certificate` | [view](3_printed_declarations/mem_bigcat_exists.md) |
| `bigcat_filter_eq_filter_bigcat` | Lemma | `Prosa.Util.Bigcat.bigcat_filter_eq_filter_bigcat` | `bigcat_filter_eq_filter_bigcat_statement_certificate` | [view](3_printed_declarations/bigcat_filter_eq_filter_bigcat.md) |
| `bigcat_uniq` | Lemma | `Prosa.Util.Bigcat.bigcat_uniq` | `bigcat_uniq_statement_certificate` | [view](3_printed_declarations/bigcat_uniq.md) |
| `seq_different_elements_nil` | Lemma | `Prosa.Util.Bigcat.seq_different_elements_nil` | `seq_different_elements_nil_statement_certificate` | [view](3_printed_declarations/seq_different_elements_nil.md) |
| `bigcat_seq_uniqK` | Lemma | `Prosa.Util.Bigcat.bigcat_seq_uniqK` | `bigcat_seq_uniqK_statement_certificate` | [view](3_printed_declarations/bigcat_seq_uniqK.md) |
| `bigcat_partitions` | Lemma | `Prosa.Util.Bigcat.bigcat_partitions` | `bigcat_partitions_statement_certificate` | [view](3_printed_declarations/bigcat_partitions.md) |

## Certificates

| Module | Role |
|---|---|
| [`BigcatCertificate`](4_correspondence/BigcatCertificate.v) | Encoded target statements use the canonical representatives of the approved eqType/DecidableEq and ordered seq/List relations. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `BcTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
