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
| `ArrivalSequenceBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedSbfFacts` |
| `FsScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedSbfFacts`; module named `FsScheduleBaseAdapter` |
| `SupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedSbfFacts`; module named `SupplyBaseAdapter` |
| `SupplyScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedSbfFacts`; module named `SupplyScheduleBaseAdapter` |
| `ArrivalSequenceOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedSbfFacts` |
| `FsScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedSbfFacts`; certificate module names in `Require` lines renamed; module named `FsScheduleFiniteOperations` |
| `SupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../shared/certificates/SupplyNatBoolOperations.v) | `ImportedSupply` → `ImportedSbfFacts` |
| `SupplyScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedSbfFacts`; certificate module names in `Require` lines renamed; module named `SupplyScheduleFiniteOperations` |
| `ArrivalSequenceCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedSbfFacts` |
| `FsScheduleCorrespondence` | [`certificates/FsScheduleCorrespondence.v`](../../../../../shared/certificates/FsScheduleCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedSbfFacts` |
| `SupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedSbfFacts`; certificate module names in `Require` lines renamed; module named `SupplyIntervalOperations` |
| `SupplyScheduleOperations` | [`certificates/SupplyScheduleOperations.v`](../../../../../shared/certificates/SupplyScheduleOperations.v) | `ImportedSupply` → `ImportedSbfFacts` |
| `FsProcessorStateCorrespondence` | [`certificates/ScheduleProcessorStateCorrespondence.v`](../../../../../shared/certificates/ScheduleProcessorStateCorrespondence.v) | `ImportedSchedule` → `ImportedSbfFacts`; certificate module names in `Require` lines renamed; module named `FsProcessorStateCorrespondence` |
| `SupplyCorrespondence` | [`certificates/SupplyCorrespondence.v`](../../../../../shared/certificates/SupplyCorrespondence.v) | `ImportedSupply` → `ImportedSbfFacts` |
| `FactsSupplyOperationCorrespondence` | [`certificates/FactsSupplyOperationCorrespondence.v`](../../../../../shared/certificates/FactsSupplyOperationCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedSbfFacts` |
| `FactsSupplyPlatformPropertiesCorrespondence` | [`certificates/FactsSupplyPlatformPropertiesCorrespondence.v`](../../../../../shared/certificates/FactsSupplyPlatformPropertiesCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedSbfFacts` |
| `PredCorrespondence` | [`certificates/PredCorrespondence.v`](../../../../../shared/certificates/PredCorrespondence.v) | `ImportedPred` → `ImportedSbfFacts` |
| `FactsSupplyStatementCorrespondence` | [`certificates/FactsSupplyStatementCorrespondence.v`](../../../../../shared/certificates/FactsSupplyStatementCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedSbfFacts` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
