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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedHyperperiod`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedHyperperiod`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedHyperperiod`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedHyperperiod` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedHyperperiod`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedHyperperiod`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedHyperperiod`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedHyperperiod`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedHyperperiod`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `PreemptionParameterCorrespondence` | [`certificates/PreemptionParameterCorrespondence.v`](../../../../../shared/certificates/PreemptionParameterCorrespondence.v) | `ImportedPreemptionParameter` → `ImportedHyperperiod` |
| `TaskOffsetCorrespondence` | [`certificates/TaskOffsetCorrespondence.v`](../../../../../shared/certificates/TaskOffsetCorrespondence.v) | `ImportedTaskOffset` → `ImportedHyperperiod` |
| `PeriodicCorrespondence` | [`certificates/PeriodicCorrespondence-2.v`](../../../../../shared/certificates/PeriodicCorrespondence-2.v) | `ImportedPeriodic` → `ImportedHyperperiod` |
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence-2.v`](../../../../../shared/certificates/NatSubCorrespondence-2.v) | `ImportedLcmseqSpec` → `ImportedHyperperiod` |
| `LcmseqBaseAdapter` | [`certificates/LcmseqBaseAdapter.v`](../../../../../shared/certificates/LcmseqBaseAdapter.v) | `ImportedLcmseqSpec` → `ImportedHyperperiod` |
| `LcmseqDivModAdapter` | [`certificates/LcmseqDivModAdapter.v`](../../../../../shared/certificates/LcmseqDivModAdapter.v) | `ImportedLcmseqSpec` → `ImportedHyperperiod` |
| `LcmseqCorrespondence` | [`certificates/LcmseqCorrespondence.v`](../../../../../shared/certificates/LcmseqCorrespondence.v) | `ImportedLcmseqSpec` → `ImportedHyperperiod` |
| `HyperperiodCorrespondence` | [`certificates/HyperperiodCorrespondence.v`](../../../../../shared/certificates/HyperperiodCorrespondence.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `TaskOffsetComputationInterface` | [`lean_interfaces/TaskOffsetComputationInterface.lean`](../../../../../shared/lean_interfaces/TaskOffsetComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `PeriodicComputationInterface` | [`lean_interfaces/PeriodicComputationInterface.lean`](../../../../../shared/lean_interfaces/PeriodicComputationInterface.lean) |
| `FactsPeriodicArrivalTimesComputationInterface` | [`lean_interfaces/FactsPeriodicArrivalTimesComputationInterface.lean`](../../../../../shared/lean_interfaces/FactsPeriodicArrivalTimesComputationInterface.lean) |
| `LcmseqSpecComputationInterface` | [`lean_interfaces/LcmseqSpecComputationInterface.lean`](../../../../../shared/lean_interfaces/LcmseqSpecComputationInterface.lean) |
