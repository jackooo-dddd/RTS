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
| `ServiceBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedFinishTime` |
| `ServiceNatBoolOperations` | [`certificates/ServiceNatBoolOperations.v`](../../../../../shared/certificates/ServiceNatBoolOperations.v) | `ImportedService` → `ImportedFinishTime` |
| `FinishTimeMinBridge` | [`certificates/FinishTimeMinBridge.v`](../../../../../shared/certificates/FinishTimeMinBridge.v) | none |
| `ServiceIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedFinishTime` |
| `ServiceJobOperations` | [`certificates/ServiceJobOperations.v`](../../../../../shared/certificates/ServiceJobOperations.v) | `ImportedService` → `ImportedFinishTime` |
| `ServiceScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedFinishTime` |
| `ServiceCorrespondence` | [`certificates/ServiceCorrespondence.v`](../../../../../shared/certificates/ServiceCorrespondence.v) | `ImportedService` → `ImportedFinishTime` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
