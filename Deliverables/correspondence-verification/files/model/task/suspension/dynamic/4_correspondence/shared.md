# Shared modules used by this file

See [`shared/README.md`](../../../../../../shared/README.md).

## Common certificates

| Module | Shared file |
|---|---|
| `LogicalRelation` | [`certificates/common/LogicalRelation.v`](../../../../../../shared/certificates/common/LogicalRelation.v) |
| `PropSPropFoundation` | [`certificates/common/PropSPropFoundation.v`](../../../../../../shared/certificates/common/PropSPropFoundation.v) |
| `SubadditivityNatCorrespondence` | [`certificates/common/SubadditivityNatCorrespondence.v`](../../../../../../shared/certificates/common/SubadditivityNatCorrespondence.v) |

## Shared certificates

| Module | Shared file | Differences in this file |
|---|---|---|
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedDynamicSuspension`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedDynamicSuspension`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedDynamicSuspension`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedDynamicSuspension`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedDynamicSuspension`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `ProgressHelpers` | [`certificates/ProgressHelpers.v`](../../../../../../shared/certificates/ProgressHelpers.v) | `ImportedSuspension` → `ImportedDynamicSuspension` |
| `SuspensionCorrespondence` | [`certificates/SuspensionCorrespondence.v`](../../../../../../shared/certificates/SuspensionCorrespondence.v) | `ImportedSuspension` → `ImportedDynamicSuspension` |
| `DynamicSuspensionCorrespondence` | [`certificates/DynamicSuspensionCorrespondence.v`](../../../../../../shared/certificates/DynamicSuspensionCorrespondence.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `ProgressComputationInterface` | [`lean_interfaces/ProgressComputationInterface.lean`](../../../../../../shared/lean_interfaces/ProgressComputationInterface.lean) |
| `SuspensionComputationInterface` | [`lean_interfaces/SuspensionComputationInterface.lean`](../../../../../../shared/lean_interfaces/SuspensionComputationInterface.lean) |
