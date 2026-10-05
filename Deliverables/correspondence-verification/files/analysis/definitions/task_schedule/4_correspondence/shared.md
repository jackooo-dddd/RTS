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
| `ArrivalSequenceBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedTaskSchedule` |
| `ServiceBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedTaskSchedule` |
| `ServiceNatBoolOperations` | [`certificates/ServiceNatBoolOperations.v`](../../../../../shared/certificates/ServiceNatBoolOperations.v) | `ImportedService` → `ImportedTaskSchedule` |
| `ServiceIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedTaskSchedule` |
| `ServiceScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedTaskSchedule` |
| `TaskScheduleCorrespondence` | [`certificates/TaskScheduleCorrespondence.v`](../../../../../shared/certificates/TaskScheduleCorrespondence.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
