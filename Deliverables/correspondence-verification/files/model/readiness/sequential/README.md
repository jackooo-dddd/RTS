# `model/readiness/sequential.v`

This file has no public declarations in the v0.6 declaration inventory: it declares notations, local instances or re-exports other modules. It was accepted as a whole file. Its local `sequential_ready_instance` is certified by the certificates below, as a helper that is not counted.

## Certificates

| Module | Role |
|---|---|
| [`ReadinessSequentialCorrespondence`](4_correspondence/ReadinessSequentialCorrespondence.v) | Certificates for the named source-local instance of `model/readiness/sequential.v`: for related inputs (task map, job arrival/cost, processor state, arrival sequence, schedule) the `job_ready` field … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
