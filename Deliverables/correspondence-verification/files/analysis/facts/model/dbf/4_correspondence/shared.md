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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedFactsDbf`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedFactsDbf`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedFactsDbf`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedFactsDbf` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedFactsDbf`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsDbf`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedFactsDbf`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedFactsDbf`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsDbf`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `PreemptionParameterCorrespondence` | [`certificates/PreemptionParameterCorrespondence.v`](../../../../../../shared/certificates/PreemptionParameterCorrespondence.v) | `ImportedPreemptionParameter` → `ImportedFactsDbf` |
| `WorkloadCorrespondence` | [`certificates/WorkloadCorrespondence.v`](../../../../../../shared/certificates/WorkloadCorrespondence.v) | `ImportedWorkload` → `ImportedFactsDbf` |
| `CurvesCorrespondence` | [`certificates/CurvesCorrespondence.v`](../../../../../../shared/certificates/CurvesCorrespondence.v) | `ImportedCurves` → `ImportedFactsDbf` |
| `RequestBoundFunctionCorrespondence` | [`certificates/RequestBoundFunctionCorrespondence.v`](../../../../../../shared/certificates/RequestBoundFunctionCorrespondence.v) | `ImportedRequestBoundFunction` → `ImportedFactsDbf` |
| `WorkloadBoundedCorrespondence` | [`certificates/WorkloadBoundedCorrespondence.v`](../../../../../../shared/certificates/WorkloadBoundedCorrespondence.v) | `ImportedWorkloadBounded` → `ImportedFactsDbf` |
| `DemandBoundFunctionCorrespondence` | [`certificates/DemandBoundFunctionCorrespondence.v`](../../../../../../shared/certificates/DemandBoundFunctionCorrespondence.v) | `ImportedDemandBoundFunction` → `ImportedFactsDbf` |

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
| `DemandBoundFunctionComputationInterface` | [`lean_interfaces/DemandBoundFunctionComputationInterface.lean`](../../../../../../shared/lean_interfaces/DemandBoundFunctionComputationInterface.lean) |
