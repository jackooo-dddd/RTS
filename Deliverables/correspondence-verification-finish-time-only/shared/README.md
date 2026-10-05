# Shared modules

Modules used by more than one file. Each file's `4_correspondence/shared.md` lists the ones it uses.

## Certificates used unchanged: [`certificates/common/`](certificates/common/)

These modules do not mention any particular file's Lean declarations, so every file uses the same source unchanged.

| Module | Content |
|---|---|
| [`PropSPropFoundation.v`](certificates/common/PropSPropFoundation.v) | `PropSPropRel`, which pairs a Rocq `Prop` with an imported Lean `SProp`, with maps in both directions; also the single foundation axiom `interpret_strict` |
| [`LogicalRelation.v`](certificates/common/LogicalRelation.v) | The introduction rule for `PropSPropRel` |
| [`SubadditivityNatCorrespondence.v`](certificates/common/SubadditivityNatCorrespondence.v) | `SubNatRel`, relating Rocq `nat` and Lean `Nat`, with `+`, `*`, `≤`, `<` and `=`. Its Lean arithmetic comes from one fixed shared import, not from a file's own import. |

## Re-bound certificates: [`certificates/behavior_service/`](certificates/behavior_service/)

These modules state relations about imported Lean definitions (Booleans, lists, Nat operations, service sums,
schedules, job cost and arrival). They were accepted for `behavior/service.v`, where they refer to that file's
imported module, `ImportedService`.

Each translated file's Lean code is imported into Rocq as its own module. A file that uses these relations therefore
uses them **re-bound**: the module here with the imported module name replaced by the file's own (for example
`ImportedService` → `ImportedFinishTime`), and nothing else changed. Each file's `shared.md` records that substitution.
During validation the re-bound module is recompiled against the file's import, so its proofs are checked again for
each file.

| Module | Content |
|---|---|
| [`ServiceBaseAdapter.v`](certificates/behavior_service/ServiceBaseAdapter.v) | Booleans, lists, membership |
| [`ServiceNatBoolOperations.v`](certificates/behavior_service/ServiceNatBoolOperations.v) | Nat and Boolean operations |
| [`ServiceIntervalOperations.v`](certificates/behavior_service/ServiceIntervalOperations.v) | Sums over half-open intervals |
| [`ServiceScheduleOperations.v`](certificates/behavior_service/ServiceScheduleOperations.v) | Processor states and schedules |
| [`ServiceJobOperations.v`](certificates/behavior_service/ServiceJobOperations.v) | Job cost and arrival |
| [`ServiceCorrespondence.v`](certificates/behavior_service/ServiceCorrespondence.v) | `scheduled_at`, `service`, `completed_by`, `completes_at`, `job_response_time_bound`, … |

## Lean interfaces: [`lean_interfaces/`](lean_interfaces/)

Validation-only Lean equations, proved in Lean and exported with their proofs, that certificates of several files refer
to.

| Interface | Content |
|---|---|
| [`ServiceComputationInterface.lean`](lean_interfaces/ServiceComputationInterface.lean) | List-based forms of `scheduled_at`, `service_at`, `service`, `completed_by`, `pending`, …; each is checked by the Lean kernel to equal the production definition |
