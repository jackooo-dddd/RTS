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
| `FsScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedFactsBehaviorSupply`; module named `FsScheduleBaseAdapter` |
| `SupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedFactsBehaviorSupply`; module named `SupplyBaseAdapter` |
| `FsScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedFactsBehaviorSupply`; certificate module names in `Require` lines renamed; module named `FsScheduleFiniteOperations` |
| `SupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../../shared/certificates/SupplyNatBoolOperations.v) | `ImportedSupply` → `ImportedFactsBehaviorSupply` |
| `FsScheduleCorrespondence` | [`certificates/FsScheduleCorrespondence.v`](../../../../../../shared/certificates/FsScheduleCorrespondence.v) | none |
| `SupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedFactsBehaviorSupply`; certificate module names in `Require` lines renamed; module named `SupplyIntervalOperations` |
| `FsProcessorStateCorrespondence` | [`certificates/ScheduleProcessorStateCorrespondence.v`](../../../../../../shared/certificates/ScheduleProcessorStateCorrespondence.v) | `ImportedSchedule` → `ImportedFactsBehaviorSupply`; certificate module names in `Require` lines renamed; module named `FsProcessorStateCorrespondence` |
| `FactsSupplyOperationCorrespondence` | [`certificates/FactsSupplyOperationCorrespondence.v`](../../../../../../shared/certificates/FactsSupplyOperationCorrespondence.v) | none |
| `FactsSupplyPlatformPropertiesCorrespondence` | [`certificates/FactsSupplyPlatformPropertiesCorrespondence.v`](../../../../../../shared/certificates/FactsSupplyPlatformPropertiesCorrespondence.v) | none |
| `FactsSupplyStatementCorrespondence` | [`certificates/FactsSupplyStatementCorrespondence.v`](../../../../../../shared/certificates/FactsSupplyStatementCorrespondence.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
