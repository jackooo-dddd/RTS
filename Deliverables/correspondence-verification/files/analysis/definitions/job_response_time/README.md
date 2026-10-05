# `analysis/definitions/job_response_time.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_response_time_exceeds` | Definition | `Prosa.Analysis.Definitions.JobResponseTime.job_response_time_exceeds` | `job_response_time_exceeds_correspondence` | [view](3_printed_declarations/job_response_time_exceeds.md) |

## Certificates

| Module | Role |
|---|---|
| [`JobResponseTimeExactTypeGuards`](4_correspondence/JobResponseTimeExactTypeGuards.v) | Elaborated source and actual compiled target types; these checks are separate from the proof of semantic correspondence. |
| [`JobResponseTimeCorrespondence`](4_correspondence/JobResponseTimeCorrespondence.v) | Compose already certified arrival, addition, completion, and Boolean negation relations. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
