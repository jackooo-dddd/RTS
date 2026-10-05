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
| `PmJitterSvcBaseAdapter` | [`certificates/JcJitterSvcBaseAdapter.v`](../../../../../shared/certificates/JcJitterSvcBaseAdapter.v) | `ImportedFactsJobConstructor` → `ImportedPaperModel`; module named `PmJitterSvcBaseAdapter` |
| `PmJitterSvcIntervalOperations` | [`certificates/JcJitterSvcIntervalOperations.v`](../../../../../shared/certificates/JcJitterSvcIntervalOperations.v) | `ImportedFactsJobConstructor` → `ImportedPaperModel`; certificate module names in `Require` lines renamed; module named `PmJitterSvcIntervalOperations` |
| `PmFinishTimeMinBridge` | [`certificates/FinishTimeMinBridge.v`](../../../../../shared/certificates/FinishTimeMinBridge.v) | `ImportedFinishTime` → `ImportedPaperModel`; certificate module names in `Require` lines renamed; module named `PmFinishTimeMinBridge` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `ServiceOfJobsComputationInterface` | [`lean_interfaces/ServiceOfJobsComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceOfJobsComputationInterface.lean) |
| `ScheduledComputationInterface` | [`lean_interfaces/ScheduledComputationInterface.lean`](../../../../../shared/lean_interfaces/ScheduledComputationInterface.lean) |
| `IdealScheduleComputationInterface` | [`lean_interfaces/IdealScheduleComputationInterface.lean`](../../../../../shared/lean_interfaces/IdealScheduleComputationInterface.lean) |
| `CriterionComputationInterface` | [`lean_interfaces/CriterionComputationInterface.lean`](../../../../../shared/lean_interfaces/CriterionComputationInterface.lean) |
| `FinishTimeExportInterface` | [`lean_interfaces/FinishTimeExportInterface.lean`](../../../../../shared/lean_interfaces/FinishTimeExportInterface.lean) |
