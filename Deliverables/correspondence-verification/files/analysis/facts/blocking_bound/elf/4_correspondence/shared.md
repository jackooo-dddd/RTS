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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedFactsBlockingBoundElf`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedFactsBlockingBoundElf`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedFactsBlockingBoundElf`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedFactsBlockingBoundElf` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedFactsBlockingBoundElf`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsBlockingBoundElf`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedFactsBlockingBoundElf`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedFactsBlockingBoundElf`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedFactsBlockingBoundElf`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `PreemptionParameterCorrespondence` | [`certificates/PreemptionParameterCorrespondence.v`](../../../../../../shared/certificates/PreemptionParameterCorrespondence.v) | `ImportedPreemptionParameter` → `ImportedFactsBlockingBoundElf` |
| `PreemptionTimeCorrespondence` | [`certificates/PreemptionTimeCorrespondence.v`](../../../../../../shared/certificates/PreemptionTimeCorrespondence.v) | `ImportedPreemptionTime` → `ImportedFactsBlockingBoundElf` |
| `PriorityDrivenCorrespondence` | [`certificates/PriorityDrivenCorrespondence.v`](../../../../../../shared/certificates/PriorityDrivenCorrespondence.v) | `ImportedPriorityDriven` → `ImportedFactsBlockingBoundElf` |
| `PStateCoverHelpers` | [`certificates/PStateCoverHelpers-2.v`](../../../../../../shared/certificates/PStateCoverHelpers-2.v) | `ImportedExistence` → `ImportedFactsBlockingBoundElf` |
| `FactsPreemptionHelpers` | [`certificates/FactsPreemptionHelpers.v`](../../../../../../shared/certificates/FactsPreemptionHelpers.v) | `ImportedFactsJitter` → `ImportedFactsBlockingBoundElf` |
| `WorkloadCorrespondence` | [`certificates/WorkloadCorrespondence.v`](../../../../../../shared/certificates/WorkloadCorrespondence.v) | `ImportedWorkload` → `ImportedFactsBlockingBoundElf` |
| `PriorityInversionCorrespondence` | [`certificates/PriorityInversionCorrespondence.v`](../../../../../../shared/certificates/PriorityInversionCorrespondence.v) | `ImportedPriorityInversion` → `ImportedFactsBlockingBoundElf` |
| `ExistenceHelpers` | [`certificates/ExistenceHelpers.v`](../../../../../../shared/certificates/ExistenceHelpers.v) | `ImportedFactsCarryIn` → `ImportedFactsBlockingBoundElf` |
| `HepAtPtHelpers` | [`certificates/ExcHepAtPtHelpers.v`](../../../../../../shared/certificates/ExcHepAtPtHelpers.v) | `ImportedExceedanceSbf` → `ImportedFactsBlockingBoundElf`; certificate module names in `Require` lines renamed; module named `HepAtPtHelpers` |
| `TaskPreemptionParametersCorrespondence` | [`certificates/TaskPreemptionParametersCorrespondence.v`](../../../../../../shared/certificates/TaskPreemptionParametersCorrespondence.v) | `ImportedTaskPreemptionParameters` → `ImportedFactsBlockingBoundElf` |
| `BusyIntervalPiHelpers` | [`certificates/ExcBusyIntervalPiHelpers.v`](../../../../../../shared/certificates/ExcBusyIntervalPiHelpers.v) | `ImportedExceedanceSbf` → `ImportedFactsBlockingBoundElf`; certificate module names in `Require` lines renamed; module named `BusyIntervalPiHelpers` |
| `CurvesCorrespondence` | [`certificates/CurvesCorrespondence.v`](../../../../../../shared/certificates/CurvesCorrespondence.v) | `ImportedCurves` → `ImportedFactsBlockingBoundElf` |
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence.v`](../../../../../../shared/certificates/NatSubCorrespondence.v) | `ImportedNat` → `ImportedFactsBlockingBoundElf` |
| `PcoBaseAdapter` | [`certificates/PriorityBaseAdapter.v`](../../../../../../shared/certificates/PriorityBaseAdapter.v) | `ImportedPriorityDefinitions` → `ImportedFactsBlockingBoundElf`; module named `PcoBaseAdapter` |
| `PcoStaticOrder` | [`certificates/PcoStaticOrder.v`](../../../../../../shared/certificates/PcoStaticOrder.v) | `ImportedPriorityCoercion` → `ImportedFactsBlockingBoundElf` |
| `PcoDynamicOrder` | [`certificates/PcoDynamicOrder.v`](../../../../../../shared/certificates/PcoDynamicOrder.v) | `ImportedPriorityCoercion` → `ImportedFactsBlockingBoundElf` |
| `PriorityCoercionCorrespondence` | [`certificates/PriorityCoercionCorrespondence.v`](../../../../../../shared/certificates/PriorityCoercionCorrespondence.v) | `ImportedPriorityCoercion` → `ImportedFactsBlockingBoundElf` |
| `PriorityGelHelpers` | [`certificates/PriorityGelHelpers.v`](../../../../../../shared/certificates/PriorityGelHelpers.v) | `ImportedBlockingBoundElf` → `ImportedFactsBlockingBoundElf` |
| `PriorityElfHelpers` | [`certificates/PriorityElfCorrespondence.v`](../../../../../../shared/certificates/PriorityElfCorrespondence.v) | `ImportedPriorityElf` → `ImportedFactsBlockingBoundElf`; certificate module names in `Require` lines renamed; module named `PriorityElfHelpers` |
| `BlockingBoundElfCorrespondence` | [`certificates/BlockingBoundElfCorrespondence.v`](../../../../../../shared/certificates/BlockingBoundElfCorrespondence.v) | `ImportedBlockingBoundElf` → `ImportedFactsBlockingBoundElf` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `PreemptionTimeComputationInterface` | [`lean_interfaces/PreemptionTimeComputationInterface.lean`](../../../../../../shared/lean_interfaces/PreemptionTimeComputationInterface.lean) |
| `PriorityDrivenComputationInterface` | [`lean_interfaces/PriorityDrivenComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityDrivenComputationInterface.lean) |
| `ScheduledComputationInterface` | [`lean_interfaces/ScheduledComputationInterface.lean`](../../../../../../shared/lean_interfaces/ScheduledComputationInterface.lean) |
| `ProcessorStateCoverInterface` | [`lean_interfaces/ProcessorStateCoverInterface.lean`](../../../../../../shared/lean_interfaces/ProcessorStateCoverInterface.lean) |
| `FactsPreemptionComputationInterface` | [`lean_interfaces/FactsPreemptionComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsPreemptionComputationInterface.lean) |
| `BusyIntervalClassicalComputationInterface` | [`lean_interfaces/BusyIntervalClassicalComputationInterface.lean`](../../../../../../shared/lean_interfaces/BusyIntervalClassicalComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `WorkloadComputationInterface` | [`lean_interfaces/WorkloadComputationInterface.lean`](../../../../../../shared/lean_interfaces/WorkloadComputationInterface.lean) |
| `ServiceOfJobsComputationInterface` | [`lean_interfaces/ServiceOfJobsComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceOfJobsComputationInterface.lean) |
| `FactsServiceOfJobsComputationInterface` | [`lean_interfaces/FactsServiceOfJobsComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsServiceOfJobsComputationInterface.lean) |
| `PriorityInversionComputationInterface` | [`lean_interfaces/PriorityInversionComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityInversionComputationInterface.lean) |
| `WorkBearingReadinessComputationInterface` | [`lean_interfaces/WorkBearingReadinessComputationInterface.lean`](../../../../../../shared/lean_interfaces/WorkBearingReadinessComputationInterface.lean) |
| `JobPropertiesExportInterface` | [`lean_interfaces/JobPropertiesExportInterface.lean`](../../../../../../shared/lean_interfaces/JobPropertiesExportInterface.lean) |
| `ExistenceComputationInterface` | [`lean_interfaces/ExistenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ExistenceComputationInterface.lean) |
| `HepAtPtComputationInterface` | [`lean_interfaces/HepAtPtComputationInterface.lean`](../../../../../../shared/lean_interfaces/HepAtPtComputationInterface.lean) |
| `TaskPreemptionParametersComputationInterface` | [`lean_interfaces/TaskPreemptionParametersComputationInterface.lean`](../../../../../../shared/lean_interfaces/TaskPreemptionParametersComputationInterface.lean) |
| `PiComputationInterface` | [`lean_interfaces/PiComputationInterface.lean`](../../../../../../shared/lean_interfaces/PiComputationInterface.lean) |
| `BlockingBoundEdfComputationInterface` | [`lean_interfaces/BlockingBoundEdfComputationInterface.lean`](../../../../../../shared/lean_interfaces/BlockingBoundEdfComputationInterface.lean) |
| `BlockingBoundEdfFactsComputationInterface` | [`lean_interfaces/BlockingBoundEdfFactsComputationInterface.lean`](../../../../../../shared/lean_interfaces/BlockingBoundEdfFactsComputationInterface.lean) |
| `BlockingBoundFpComputationInterface` | [`lean_interfaces/BlockingBoundFpComputationInterface.lean`](../../../../../../shared/lean_interfaces/BlockingBoundFpComputationInterface.lean) |
| `PriorityGelComputationInterface` | [`lean_interfaces/PriorityGelComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityGelComputationInterface.lean) |
| `PriorityElfComputationInterface` | [`lean_interfaces/PriorityElfComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityElfComputationInterface.lean) |
| `BlockingBoundElfComputationInterface` | [`lean_interfaces/BlockingBoundElfComputationInterface.lean`](../../../../../../shared/lean_interfaces/BlockingBoundElfComputationInterface.lean) |
