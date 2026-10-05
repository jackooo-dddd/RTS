# Shared modules used by this file

See [`shared/README.md`](../../../../../../../shared/README.md).

## Common certificates

| Module | Shared file |
|---|---|
| `LogicalRelation` | [`certificates/common/LogicalRelation.v`](../../../../../../../shared/certificates/common/LogicalRelation.v) |
| `PropSPropFoundation` | [`certificates/common/PropSPropFoundation.v`](../../../../../../../shared/certificates/common/PropSPropFoundation.v) |
| `SubadditivityNatCorrespondence` | [`certificates/common/SubadditivityNatCorrespondence.v`](../../../../../../../shared/certificates/common/SubadditivityNatCorrespondence.v) |

## Shared certificates

| Module | Shared file | Differences in this file |
|---|---|---|
| `ArrivalSequenceBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedFactsSbfPeriodic` |
| `ArrivalSequenceOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedFactsSbfPeriodic` |
| `ArrivalSequenceCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedFactsSbfPeriodic` |
| `SupplyScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedFactsSbfPeriodic`; module named `SupplyScheduleBaseAdapter` |
| `SupplyScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedFactsSbfPeriodic`; certificate module names in `Require` lines renamed; module named `SupplyScheduleFiniteOperations` |
| `SupplyScheduleOperations` | [`certificates/SupplyScheduleOperations.v`](../../../../../../../shared/certificates/SupplyScheduleOperations.v) | `ImportedSupply` → `ImportedFactsSbfPeriodic` |
| `SupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedFactsSbfPeriodic`; module named `SupplyBaseAdapter` |
| `SupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../../../shared/certificates/SupplyNatBoolOperations.v) | `ImportedSupply` → `ImportedFactsSbfPeriodic` |
| `SupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedFactsSbfPeriodic`; certificate module names in `Require` lines renamed; module named `SupplyIntervalOperations` |
| `SupplyCorrespondence` | [`certificates/SupplyCorrespondence.v`](../../../../../../../shared/certificates/SupplyCorrespondence.v) | `ImportedSupply` → `ImportedFactsSbfPeriodic` |
| `PredCorrespondence` | [`certificates/PredCorrespondence.v`](../../../../../../../shared/certificates/PredCorrespondence.v) | `ImportedPred` → `ImportedFactsSbfPeriodic` |
| `PlainCorrespondence` | [`certificates/PlainCorrespondence.v`](../../../../../../../shared/certificates/PlainCorrespondence.v) | `ImportedPlain` → `ImportedFactsSbfPeriodic` |
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence.v`](../../../../../../../shared/certificates/NatSubCorrespondence.v) | `ImportedNat` → `ImportedFactsSbfPeriodic` |
| `DivModCorrespondence` | [`certificates/DivModCorrespondence.v`](../../../../../../../shared/certificates/DivModCorrespondence.v) | `ImportedDivMod ImportedNat` → `ImportedFactsSbfPeriodic` |
| `PeriodicCorrespondence` | [`certificates/PeriodicCorrespondence.v`](../../../../../../../shared/certificates/PeriodicCorrespondence.v) | `ImportedPeriodic` → `ImportedFactsSbfPeriodic` |
| `FsScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedFactsSbfPeriodic`; module named `FsScheduleBaseAdapter` |
| `FsScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedFactsSbfPeriodic`; certificate module names in `Require` lines renamed; module named `FsScheduleFiniteOperations` |
| `FsScheduleCorrespondence` | [`certificates/FsScheduleCorrespondence.v`](../../../../../../../shared/certificates/FsScheduleCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedFactsSbfPeriodic` |
| `FsProcessorStateCorrespondence` | [`certificates/ScheduleProcessorStateCorrespondence.v`](../../../../../../../shared/certificates/ScheduleProcessorStateCorrespondence.v) | `ImportedSchedule` → `ImportedFactsSbfPeriodic`; certificate module names in `Require` lines renamed; module named `FsProcessorStateCorrespondence` |
| `FactsSupplyPlatformPropertiesCorrespondence` | [`certificates/FactsSupplyPlatformPropertiesCorrespondence.v`](../../../../../../../shared/certificates/FactsSupplyPlatformPropertiesCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedFactsSbfPeriodic` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `SupplyComputationInterface` | [`lean_interfaces/SupplyComputationInterface.lean`](../../../../../../../shared/lean_interfaces/SupplyComputationInterface.lean) |
| `PlatformPropertiesComputationInterface` | [`lean_interfaces/PlatformPropertiesComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PlatformPropertiesComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `DivModComputationInterface` | [`lean_interfaces/DivModComputationInterface.lean`](../../../../../../../shared/lean_interfaces/DivModComputationInterface.lean) |
| `PredExportInterface` | [`lean_interfaces/PredExportInterface.lean`](../../../../../../../shared/lean_interfaces/PredExportInterface.lean) |
