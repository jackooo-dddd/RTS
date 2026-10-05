# `util/lcmseq.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `lcml` | Definition | `Prosa.Util.Lcmseq.lcml` | `lcml_correspondence` | [view](3_printed_declarations/lcml.md) |
| `int_divides_lcm_in_seq` | Lemma | `Prosa.Util.Lcmseq.int_divides_lcm_in_seq` | `int_divides_lcm_in_seq_correspondence` | [view](3_printed_declarations/int_divides_lcm_in_seq.md) |
| `lcm_seq_divides_lcm_super` | Lemma | `Prosa.Util.Lcmseq.lcm_seq_divides_lcm_super` | `lcm_seq_divides_lcm_super_correspondence` | [view](3_printed_declarations/lcm_seq_divides_lcm_super.md) |
| `lcm_seq_is_mult_of_all_ints` | Lemma | `Prosa.Util.Lcmseq.lcm_seq_is_mult_of_all_ints` | `lcm_seq_is_mult_of_all_ints_correspondence` | [view](3_printed_declarations/lcm_seq_is_mult_of_all_ints.md) |
| `all_pos_implies_lcml_pos` | Lemma | `Prosa.Util.Lcmseq.all_pos_implies_lcml_pos` | `all_pos_implies_lcml_pos_correspondence` | [view](3_printed_declarations/all_pos_implies_lcml_pos.md) |

## Certificates

| Module | Role |
|---|---|
| [`LcmseqCertificate`](4_correspondence/LcmseqCertificate.v) | These target propositions use the exact imported operations. |
| [`LcmseqSpecCorrespondence`](4_correspondence/LcmseqSpecCorrespondence.v) | The per-declaration certificates of `util/lcmseq.v` under the names the publisher expects. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Quot_sound`, `propext` |
| Definitional UIP | `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
