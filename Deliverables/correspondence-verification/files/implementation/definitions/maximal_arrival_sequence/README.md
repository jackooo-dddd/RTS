# `implementation/definitions/maximal_arrival_sequence.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `suffix_sum` | Definition | `Prosa.Implementation.Definitions.MaximalArrivalSequence.suffix_sum` | `suffix_sum_correspondence` | [view](3_printed_declarations/suffix_sum.md) |
| `jobs_remaining` | Definition | `Prosa.Implementation.Definitions.MaximalArrivalSequence.jobs_remaining` | `jobs_remaining_correspondence` | [view](3_printed_declarations/jobs_remaining.md) |
| `next_max_arrival` | Definition | `Prosa.Implementation.Definitions.MaximalArrivalSequence.next_max_arrival` | `next_max_arrival_correspondence` | [view](3_printed_declarations/next_max_arrival.md) |
| `extend_arrival_prefix` | Definition | `Prosa.Implementation.Definitions.MaximalArrivalSequence.extend_arrival_prefix` | `extend_arrival_prefix_correspondence` | [view](3_printed_declarations/extend_arrival_prefix.md) |
| `maximal_arrival_prefix` | Definition | `Prosa.Implementation.Definitions.MaximalArrivalSequence.maximal_arrival_prefix` | `maximal_arrival_prefix_correspondence` | [view](3_printed_declarations/maximal_arrival_prefix.md) |
| `max_arrivals_at` | Definition | `Prosa.Implementation.Definitions.MaximalArrivalSequence.max_arrivals_at` | `max_arrivals_at_correspondence` | [view](3_printed_declarations/max_arrivals_at.md) |
| `concrete_arrival_sequence` | Definition | `Prosa.Implementation.Definitions.MaximalArrivalSequence.concrete_arrival_sequence` | `concrete_arrival_sequence_correspondence` | [view](3_printed_declarations/concrete_arrival_sequence.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
