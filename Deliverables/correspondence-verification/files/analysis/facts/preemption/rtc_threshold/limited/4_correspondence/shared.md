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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedFactsRtcLimited`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedFactsRtcLimited`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedFactsRtcLimited`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedFactsRtcLimited`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsRtcLimited`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedFactsRtcLimited`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedFactsRtcLimited`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsRtcLimited`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `PreemptionParameterCorrespondence` | [`certificates/PreemptionParameterCorrespondence.v`](../../../../../../../shared/certificates/PreemptionParameterCorrespondence.v) | `ImportedPreemptionParameter` → `ImportedFactsRtcLimited` |
| `LimitedPreemptiveCorrespondence` | [`certificates/LimitedPreemptiveCorrespondence.v`](../../../../../../../shared/certificates/LimitedPreemptiveCorrespondence.v) | `ImportedLimitedPreemptive` → `ImportedFactsRtcLimited` |
| `ScheduleLimitedPreemptiveCorrespondence` | [`certificates/ScheduleLimitedPreemptiveCorrespondence.v`](../../../../../../../shared/certificates/ScheduleLimitedPreemptiveCorrespondence.v) | `ImportedScheduleLimitedPreemptive` → `ImportedFactsRtcLimited` |
| `TaskPreemptionParametersCorrespondence` | [`certificates/TaskPreemptionParametersCorrespondence.v`](../../../../../../../shared/certificates/TaskPreemptionParametersCorrespondence.v) | `ImportedTaskPreemptionParameters` → `ImportedFactsRtcLimited` |
| `TaskLimitedPreemptiveCorrespondence` | [`certificates/TaskLimitedPreemptiveCorrespondence.v`](../../../../../../../shared/certificates/TaskLimitedPreemptiveCorrespondence.v) | `ImportedTaskLimitedPreemptive` → `ImportedFactsRtcLimited` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `TaskPreemptionParametersComputationInterface` | [`lean_interfaces/TaskPreemptionParametersComputationInterface.lean`](../../../../../../../shared/lean_interfaces/TaskPreemptionParametersComputationInterface.lean) |
| `LimitedPreemptiveComputationInterface` | [`lean_interfaces/LimitedPreemptiveComputationInterface.lean`](../../../../../../../shared/lean_interfaces/LimitedPreemptiveComputationInterface.lean) |
| `TaskLimitedPreemptiveComputationInterface` | [`lean_interfaces/TaskLimitedPreemptiveComputationInterface.lean`](../../../../../../../shared/lean_interfaces/TaskLimitedPreemptiveComputationInterface.lean) |
| `ScheduleLimitedPreemptiveComputationInterface` | [`lean_interfaces/ScheduleLimitedPreemptiveComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduleLimitedPreemptiveComputationInterface.lean) |
| `FactsLimitedJobComputationInterface` | [`lean_interfaces/FactsLimitedJobComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsLimitedJobComputationInterface.lean) |
| `FactsTaskLimitedComputationInterface` | [`lean_interfaces/FactsTaskLimitedComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsTaskLimitedComputationInterface.lean) |
