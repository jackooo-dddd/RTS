# Shared modules used by this file

See [`shared/README.md`](../../../../../shared/README.md).

## Common certificates

| Module | Shared file |
|---|---|
| `LogicalRelation` | [`certificates/common/LogicalRelation.v`](../../../../../shared/certificates/common/LogicalRelation.v) |
| `PropSPropFoundation` | [`certificates/common/PropSPropFoundation.v`](../../../../../shared/certificates/common/PropSPropFoundation.v) |
| `SubadditivityNatCorrespondence` | [`certificates/common/SubadditivityNatCorrespondence.v`](../../../../../shared/certificates/common/SubadditivityNatCorrespondence.v) |

## Shared certificates

| Module | Shared file | Differences in this file |
|---|---|---|
| `OverheadsBaseAdapter` | [`certificates/OverheadsBaseAdapter.v`](../../../../../shared/certificates/OverheadsBaseAdapter.v) | none |
| `OverheadsNatBoolOperations` | [`certificates/OverheadsNatBoolOperations.v`](../../../../../shared/certificates/OverheadsNatBoolOperations.v) | none |
| `OverheadsIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedOverheads`; certificate module names in `Require` lines renamed; module named `OverheadsIntervalOperations` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
