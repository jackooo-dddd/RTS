# `analysis/abstract/ideal/abstract_seq_rta.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis` | Lemma | `Prosa.Analysis.Abstract.Ideal.AbstractSeqRta.max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis` | `max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis_correspondence` | [view](3_printed_declarations/max_in_seq_hypothesis_implies_max_in_nonseq_hypothesis.md) |
| `uniprocessor_response_time_bound_seq` | Theorem | `Prosa.Analysis.Abstract.Ideal.AbstractSeqRta.uniprocessor_response_time_bound_seq` | `uniprocessor_response_time_bound_seq_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_seq.md) |

## Certificates

| Module | Role |
|---|---|
| [`AbstractSeqRtaCorrespondence`](4_correspondence/AbstractSeqRtaCorrespondence.v) | Statement correspondences for `analysis/abstract/ideal/abstract_seq_rta.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
