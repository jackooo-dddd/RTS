# `model/composite/valid_task_arrival_sequence.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `valid_task_arrival_sequence` | Definition | `Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence` | `valid_task_arrival_sequence_correspondence` | [view](3_printed_declarations/valid_task_arrival_sequence.md) |
| `valid_task_arrival_sequence_valid_arrivals` | Lemma | `Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence_valid_arrivals` | `valid_task_arrival_sequence_valid_arrivals_correspondence` | [view](3_printed_declarations/valid_task_arrival_sequence_valid_arrivals.md) |
| `valid_task_arrival_sequence_valid_costs` | Lemma | `Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence_valid_costs` | `valid_task_arrival_sequence_valid_costs_correspondence` | [view](3_printed_declarations/valid_task_arrival_sequence_valid_costs.md) |
| `valid_task_arrival_sequence_from_taskset` | Lemma | `Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence_from_taskset` | `valid_task_arrival_sequence_from_taskset_correspondence` | [view](3_printed_declarations/valid_task_arrival_sequence_from_taskset.md) |
| `valid_task_arrival_sequence_respects_max` | Lemma | `Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence_respects_max` | `valid_task_arrival_sequence_respects_max_correspondence` | [view](3_printed_declarations/valid_task_arrival_sequence_respects_max.md) |
| `valid_task_arrival_sequence_valid_curve` | Lemma | `Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence_valid_curve` | `valid_task_arrival_sequence_valid_curve_correspondence` | [view](3_printed_declarations/valid_task_arrival_sequence_valid_curve.md) |

## Certificates

| Module | Role |
|---|---|
| [`VtasCorrespondence`](4_correspondence/VtasCorrespondence.v) | Certificates for `model/composite/valid_task_arrival_sequence.v`: the definition (related inputs give related propositions) and the five projection lemmas (source: exact elaborated type of the pinned … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
