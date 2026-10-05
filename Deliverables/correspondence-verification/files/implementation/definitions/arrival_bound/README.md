# `implementation/definitions/arrival_bound.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `task_arrivals_bound` | Inductive | `Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound` | `ab_source_constructor_periodic, ab_source_constructor_prefix, ab_source_roundtrip, ab_source_constructor_sporadic, ab_target_roundtrip` | [view](3_printed_declarations/task_arrivals_bound.md) |
| `task_arrivals_bound_eqdef` | Definition | `Prosa.Implementation.Definitions.ArrivalBound.task_arrivals_bound_eqdef` | `ab_eqdef_bool_correspondence` | [view](3_printed_declarations/task_arrivals_bound_eqdef.md) |
| `eqn_task_arrivals_bound` | Lemma | `Prosa.Implementation.Definitions.ArrivalBound.eqn_task_arrivals_bound` | `ab_eqn_task_arrivals_bound_statement_correspondence` | [view](3_printed_declarations/eqn_task_arrivals_bound.md) |

## Certificates

| Module | Role |
|---|---|
| [`ArrivalBoundArtifactAdapter`](4_correspondence/ArrivalBoundArtifactAdapter.v) | Artifact-local datatype adapter. |
| [`ArrivalBoundCorrespondence`](4_correspondence/ArrivalBoundCorrespondence.v) | Proved from the byte-identical source definition, not from the source `eqn_task_arrivals_bound` theorem proof. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
