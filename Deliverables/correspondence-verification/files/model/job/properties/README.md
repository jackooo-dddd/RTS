# `model/job/properties.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_cost_positive` | Definition | `Prosa.Model.Job.Properties.job_cost_positive` | `job_cost_positive_correspondence` | [view](3_printed_declarations/job_cost_positive.md) |
| `arrivals_have_positive_job_costs` | Definition | `Prosa.Model.Job.Properties.arrivals_have_positive_job_costs` | `arrivals_have_positive_job_costs_correspondence` | [view](3_printed_declarations/arrivals_have_positive_job_costs.md) |

## Certificates

| Module | Role |
|---|---|
| [`JobPropertiesBaseAdapter`](4_correspondence/JobPropertiesBaseAdapter.v) | Proves or defines `jp_false_elim`, `jp_false_to_strict`, `jp_coq_false_to_target` and 23 more. |
| [`JobPropertiesExactTypeGuards`](4_correspondence/JobPropertiesExactTypeGuards.v) | No description in the module. |
| [`JobPropertiesOperations`](4_correspondence/JobPropertiesOperations.v) | Minimal artifact-local operations needed by both v0.6 job-property definitions. |
| [`JobPropertiesCorrespondence`](4_correspondence/JobPropertiesCorrespondence.v) | Both certificates refer to the official v0.6 definitions and this run's actual imported compiled Lean definitions. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `propext` |
| Definitional UIP | `HEq_inst1`, `JpTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
