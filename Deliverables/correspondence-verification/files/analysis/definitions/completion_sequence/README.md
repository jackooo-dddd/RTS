# `analysis/definitions/completion_sequence.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `completion_sequence` | Definition | `Prosa.Analysis.Definitions.CompletionSequence.completion_sequence` | `completion_sequence_correspondence` | [view](3_printed_declarations/completion_sequence.md) |

## Certificates

| Module | Role |
|---|---|
| [`CompletionSequenceCorrespondence`](4_correspondence/CompletionSequenceCorrespondence.v) | Composition of the accepted arrivals_up_to, completes_at, and ordered filter correspondences, replayed against this exact combined import. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
