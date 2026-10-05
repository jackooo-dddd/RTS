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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedFactsElfAthepBound`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedFactsElfAthepBound`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedFactsElfAthepBound`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedFactsElfAthepBound` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedFactsElfAthepBound`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsElfAthepBound`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedFactsElfAthepBound`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedFactsElfAthepBound`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsElfAthepBound`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `PreemptionParameterCorrespondence` | [`certificates/PreemptionParameterCorrespondence.v`](../../../../../../shared/certificates/PreemptionParameterCorrespondence.v) | `ImportedPreemptionParameter` → `ImportedFactsElfAthepBound` |
| `WorkloadCorrespondence` | [`certificates/WorkloadCorrespondence.v`](../../../../../../shared/certificates/WorkloadCorrespondence.v) | `ImportedWorkload` → `ImportedFactsElfAthepBound` |
| `CurvesCorrespondence` | [`certificates/CurvesCorrespondence.v`](../../../../../../shared/certificates/CurvesCorrespondence.v) | `ImportedCurves` → `ImportedFactsElfAthepBound` |
| `RequestBoundFunctionCorrespondence` | [`certificates/RequestBoundFunctionCorrespondence.v`](../../../../../../shared/certificates/RequestBoundFunctionCorrespondence.v) | `ImportedRequestBoundFunction` → `ImportedFactsElfAthepBound` |
| `WorkloadBoundedCorrespondence` | [`certificates/WorkloadBoundedCorrespondence.v`](../../../../../../shared/certificates/WorkloadBoundedCorrespondence.v) | `ImportedWorkloadBounded` → `ImportedFactsElfAthepBound` |
| `EdfAthepBoundCorrespondence` | [`certificates/EdfAthepBoundCorrespondence.v`](../../../../../../shared/certificates/EdfAthepBoundCorrespondence.v) | `ImportedEdfAthepBound` → `ImportedFactsElfAthepBound` |
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence.v`](../../../../../../shared/certificates/NatSubCorrespondence.v) | `ImportedNat` → `ImportedFactsElfAthepBound` |
| `PcoBaseAdapter` | [`certificates/PriorityBaseAdapter.v`](../../../../../../shared/certificates/PriorityBaseAdapter.v) | `ImportedPriorityDefinitions` → `ImportedFactsElfAthepBound`; module named `PcoBaseAdapter` |
| `PcoStaticOrder` | [`certificates/PcoStaticOrder.v`](../../../../../../shared/certificates/PcoStaticOrder.v) | `ImportedPriorityCoercion` → `ImportedFactsElfAthepBound` |
| `PcoDynamicOrder` | [`certificates/PcoDynamicOrder.v`](../../../../../../shared/certificates/PcoDynamicOrder.v) | `ImportedPriorityCoercion` → `ImportedFactsElfAthepBound` |
| `PriorityCoercionCorrespondence` | [`certificates/PriorityCoercionCorrespondence.v`](../../../../../../shared/certificates/PriorityCoercionCorrespondence.v) | `ImportedPriorityCoercion` → `ImportedFactsElfAthepBound` |
| `PriorityGelHelpers` | [`certificates/PriorityGelHelpers.v`](../../../../../../shared/certificates/PriorityGelHelpers.v) | `ImportedBlockingBoundElf` → `ImportedFactsElfAthepBound` |
| `PriorityElfHelpers` | [`certificates/PriorityElfCorrespondence.v`](../../../../../../shared/certificates/PriorityElfCorrespondence.v) | `ImportedPriorityElf` → `ImportedFactsElfAthepBound`; certificate module names in `Require` lines renamed; module named `PriorityElfHelpers` |
| `ElfAthepBoundCorrespondence` | [`certificates/ElfAthepBoundCorrespondence.v`](../../../../../../shared/certificates/ElfAthepBoundCorrespondence.v) | `ImportedElfAthepBound` → `ImportedFactsElfAthepBound` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `BusyIntervalClassicalComputationInterface` | [`lean_interfaces/BusyIntervalClassicalComputationInterface.lean`](../../../../../../shared/lean_interfaces/BusyIntervalClassicalComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `WorkloadComputationInterface` | [`lean_interfaces/WorkloadComputationInterface.lean`](../../../../../../shared/lean_interfaces/WorkloadComputationInterface.lean) |
| `WorkloadBoundedComputationInterface` | [`lean_interfaces/WorkloadBoundedComputationInterface.lean`](../../../../../../shared/lean_interfaces/WorkloadBoundedComputationInterface.lean) |
| `RequestBoundFunctionComputationInterface` | [`lean_interfaces/RequestBoundFunctionComputationInterface.lean`](../../../../../../shared/lean_interfaces/RequestBoundFunctionComputationInterface.lean) |
| `CurvesComputationInterface` | [`lean_interfaces/CurvesComputationInterface.lean`](../../../../../../shared/lean_interfaces/CurvesComputationInterface.lean) |
| `ProcessorStateCoverInterface` | [`lean_interfaces/ProcessorStateCoverInterface.lean`](../../../../../../shared/lean_interfaces/ProcessorStateCoverInterface.lean) |
| `EdfAthepBoundComputationInterface` | [`lean_interfaces/EdfAthepBoundComputationInterface.lean`](../../../../../../shared/lean_interfaces/EdfAthepBoundComputationInterface.lean) |
| `FactsEdfAthepBoundComputationInterface` | [`lean_interfaces/FactsEdfAthepBoundComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsEdfAthepBoundComputationInterface.lean) |
| `PriorityGelComputationInterface` | [`lean_interfaces/PriorityGelComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityGelComputationInterface.lean) |
| `PriorityElfComputationInterface` | [`lean_interfaces/PriorityElfComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityElfComputationInterface.lean) |
| `ElfAthepBoundComputationInterface` | [`lean_interfaces/ElfAthepBoundComputationInterface.lean`](../../../../../../shared/lean_interfaces/ElfAthepBoundComputationInterface.lean) |
