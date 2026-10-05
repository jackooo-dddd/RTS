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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedElfAthepBound`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedElfAthepBound`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedElfAthepBound`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedElfAthepBound`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedElfAthepBound`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedElfAthepBound`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedElfAthepBound`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedElfAthepBound`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `PreemptionParameterCorrespondence` | [`certificates/PreemptionParameterCorrespondence.v`](../../../../../../shared/certificates/PreemptionParameterCorrespondence.v) | `ImportedPreemptionParameter` → `ImportedElfAthepBound` |
| `RequestBoundFunctionCorrespondence` | [`certificates/RequestBoundFunctionCorrespondence.v`](../../../../../../shared/certificates/RequestBoundFunctionCorrespondence.v) | `ImportedRequestBoundFunction` → `ImportedElfAthepBound` |
| `EdfAthepBoundCorrespondence` | [`certificates/EdfAthepBoundCorrespondence.v`](../../../../../../shared/certificates/EdfAthepBoundCorrespondence.v) | `ImportedEdfAthepBound` → `ImportedElfAthepBound` |
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence.v`](../../../../../../shared/certificates/NatSubCorrespondence.v) | `ImportedNat` → `ImportedElfAthepBound` |
| `PcoBaseAdapter` | [`certificates/PriorityBaseAdapter.v`](../../../../../../shared/certificates/PriorityBaseAdapter.v) | `ImportedPriorityDefinitions` → `ImportedElfAthepBound`; module named `PcoBaseAdapter` |
| `PcoStaticOrder` | [`certificates/PcoStaticOrder.v`](../../../../../../shared/certificates/PcoStaticOrder.v) | `ImportedPriorityCoercion` → `ImportedElfAthepBound` |
| `PcoDynamicOrder` | [`certificates/PcoDynamicOrder.v`](../../../../../../shared/certificates/PcoDynamicOrder.v) | `ImportedPriorityCoercion` → `ImportedElfAthepBound` |
| `PriorityCoercionCorrespondence` | [`certificates/PriorityCoercionCorrespondence.v`](../../../../../../shared/certificates/PriorityCoercionCorrespondence.v) | `ImportedPriorityCoercion` → `ImportedElfAthepBound` |
| `PriorityGelHelpers` | [`certificates/PriorityGelHelpers.v`](../../../../../../shared/certificates/PriorityGelHelpers.v) | `ImportedBlockingBoundElf` → `ImportedElfAthepBound` |
| `ElfAthepBoundCorrespondence` | [`certificates/ElfAthepBoundCorrespondence.v`](../../../../../../shared/certificates/ElfAthepBoundCorrespondence.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `RequestBoundFunctionComputationInterface` | [`lean_interfaces/RequestBoundFunctionComputationInterface.lean`](../../../../../../shared/lean_interfaces/RequestBoundFunctionComputationInterface.lean) |
| `EdfAthepBoundComputationInterface` | [`lean_interfaces/EdfAthepBoundComputationInterface.lean`](../../../../../../shared/lean_interfaces/EdfAthepBoundComputationInterface.lean) |
| `PriorityGelComputationInterface` | [`lean_interfaces/PriorityGelComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityGelComputationInterface.lean) |
| `PriorityElfComputationInterface` | [`lean_interfaces/PriorityElfComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityElfComputationInterface.lean) |
