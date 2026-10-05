# `model/priority/fifo.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `FIFO` | Instance | `Prosa.Model.Priority.Fifo.FIFO` | `FIFO_correspondence` | [view](3_printed_declarations/FIFO.md) |
| `FIFO_is_reflexive` | Lemma | `Prosa.Model.Priority.Fifo.FIFO_is_reflexive` | `FIFO_is_reflexive_correspondence` | [view](3_printed_declarations/FIFO_is_reflexive.md) |
| `FIFO_is_transitive` | Lemma | `Prosa.Model.Priority.Fifo.FIFO_is_transitive` | `FIFO_is_transitive_correspondence` | [view](3_printed_declarations/FIFO_is_transitive.md) |
| `FIFO_is_total` | Lemma | `Prosa.Model.Priority.Fifo.FIFO_is_total` | `FIFO_is_total_correspondence` | [view](3_printed_declarations/FIFO_is_total.md) |

## Certificates

| Module | Role |
|---|---|
| [`PriorityFifoCorrespondence`](4_correspondence/PriorityFifoCorrespondence.v) | Certificates for `model/priority/fifo.v`: the parameter class (`JobArrival`) is related pointwise on Nat with two-way totals; the policy instance(s) are related as `PdJLFPRel` for related parameters; … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `HEq_inst1`, `PdTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
