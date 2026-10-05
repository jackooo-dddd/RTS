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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedFactsDynamicSuspension`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedFactsDynamicSuspension`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedFactsDynamicSuspension`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedFactsDynamicSuspension` |
| `CurvesCorrespondence` | [`certificates/CurvesCorrespondence.v`](../../../../../../shared/certificates/CurvesCorrespondence.v) | `ImportedCurves` → `ImportedFactsDynamicSuspension` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedFactsDynamicSuspension`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsDynamicSuspension`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedFactsDynamicSuspension`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedFactsDynamicSuspension`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsDynamicSuspension`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `ProgressHelpers` | [`certificates/ProgressHelpers.v`](../../../../../../shared/certificates/ProgressHelpers.v) | `ImportedSuspension` → `ImportedFactsDynamicSuspension` |
| `SuspensionCorrespondence` | [`certificates/SuspensionCorrespondence.v`](../../../../../../shared/certificates/SuspensionCorrespondence.v) | `ImportedSuspension` → `ImportedFactsDynamicSuspension` |
| `DynamicSuspensionCorrespondence` | [`certificates/DynamicSuspensionCorrespondence.v`](../../../../../../shared/certificates/DynamicSuspensionCorrespondence.v) | `ImportedDynamicSuspension` → `ImportedFactsDynamicSuspension` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `ProgressComputationInterface` | [`lean_interfaces/ProgressComputationInterface.lean`](../../../../../../shared/lean_interfaces/ProgressComputationInterface.lean) |
| `SuspensionComputationInterface` | [`lean_interfaces/SuspensionComputationInterface.lean`](../../../../../../shared/lean_interfaces/SuspensionComputationInterface.lean) |
| `DynamicSuspensionComputationInterface` | [`lean_interfaces/DynamicSuspensionComputationInterface.lean`](../../../../../../shared/lean_interfaces/DynamicSuspensionComputationInterface.lean) |
| `FactsSuspensionComputationInterface` | [`lean_interfaces/FactsSuspensionComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsSuspensionComputationInterface.lean) |
| `FactsArrivalCurvesComputationInterface` | [`lean_interfaces/FactsArrivalCurvesComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsArrivalCurvesComputationInterface.lean) |
| `ProcessorStateCoverInterface` | [`lean_interfaces/ProcessorStateCoverInterface.lean`](../../../../../../shared/lean_interfaces/ProcessorStateCoverInterface.lean) |
