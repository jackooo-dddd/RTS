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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyNonpreemptive`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `WorkloadCorrespondence` | [`certificates/WorkloadCorrespondence.v`](../../../../../../../shared/certificates/WorkloadCorrespondence.v) | `ImportedWorkload` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractDefinitionsBaseAdapter` | [`certificates/AbstractDefinitionsBaseAdapter.v`](../../../../../../../shared/certificates/AbstractDefinitionsBaseAdapter.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ServiceBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ServiceNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `ServiceNatBoolOperations` |
| `AbstractDefinitionsArrivalOperations` | [`certificates/AbstractDefinitionsArrivalOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsArrivalOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractDefinitionsClasses` | [`certificates/AbstractDefinitionsClasses.v`](../../../../../../../shared/certificates/AbstractDefinitionsClasses.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractDefinitionsNatBoolOperations` | [`certificates/AbstractDefinitionsNatBoolOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsNatBoolOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractDefinitionsIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `AbstractDefinitionsIntervalOperations` |
| `AbstractDefinitionsOperations` | [`certificates/AbstractDefinitionsOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractDefinitionsSums` | [`certificates/AbstractDefinitionsSums.v`](../../../../../../../shared/certificates/AbstractDefinitionsSums.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractDefinitionsLogical` | [`certificates/AbstractDefinitionsLogical.v`](../../../../../../../shared/certificates/AbstractDefinitionsLogical.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ServiceIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ServiceScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractDefinitionsPendingOperations` | [`certificates/AbstractDefinitionsPendingOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsPendingOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractDefinitionsTaskOperations` | [`certificates/AbstractDefinitionsTaskOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsTaskOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractDefinitionsBusyIntervalHelpers` | [`certificates/AbstractDefinitionsBusyIntervalHelpers.v`](../../../../../../../shared/certificates/AbstractDefinitionsBusyIntervalHelpers.v) | `ImportedBusyPrefix` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `AbstractRtaHelpers` | [`certificates/AbstractRtaHelpers.v`](../../../../../../../shared/certificates/AbstractRtaHelpers.v) | `ImportedIbfSupply` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedRtaPrmEdfFullyNonpreemptive`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `PreemptionParameterCorrespondence` | [`certificates/PreemptionParameterCorrespondence.v`](../../../../../../../shared/certificates/PreemptionParameterCorrespondence.v) | `ImportedPreemptionParameter` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `TaskPreemptionParametersCorrespondence` | [`certificates/TaskPreemptionParametersCorrespondence.v`](../../../../../../../shared/certificates/TaskPreemptionParametersCorrespondence.v) | `ImportedTaskPreemptionParameters` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `IdealAbstractRtaHelpers` | [`certificates/IdealAbstractRtaHelpers.v`](../../../../../../../shared/certificates/IdealAbstractRtaHelpers.v) | `ImportedIbfTask` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ArrivalSequenceBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ArrivalSequenceOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `TaskScheduleCorrespondence` | [`certificates/TaskScheduleCorrespondence.v`](../../../../../../../shared/certificates/TaskScheduleCorrespondence.v) | `ImportedTaskSchedule` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `CurvesCorrespondence` | [`certificates/CurvesCorrespondence.v`](../../../../../../../shared/certificates/CurvesCorrespondence.v) | `ImportedCurves` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `RequestBoundFunctionCorrespondence` | [`certificates/RequestBoundFunctionCorrespondence.v`](../../../../../../../shared/certificates/RequestBoundFunctionCorrespondence.v) | `ImportedRequestBoundFunction` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `SequentialityCorrespondence` | [`certificates/SequentialityCorrespondence.v`](../../../../../../../shared/certificates/SequentialityCorrespondence.v) | `ImportedSequentiality` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ServiceOfJobsCorrespondence` | [`certificates/ServiceOfJobsCorrespondence.v`](../../../../../../../shared/certificates/ServiceOfJobsCorrespondence.v) | `ImportedServiceOfJobs` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `SupplyScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyNonpreemptive`; module named `SupplyScheduleBaseAdapter` |
| `SupplyScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `SupplyScheduleFiniteOperations` |
| `SupplyScheduleOperations` | [`certificates/SupplyScheduleOperations.v`](../../../../../../../shared/certificates/SupplyScheduleOperations.v) | `ImportedSupply` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `SupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedRtaPrmEdfFullyNonpreemptive`; module named `SupplyBaseAdapter` |
| `SupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../../../shared/certificates/SupplyNatBoolOperations.v) | `ImportedSupply` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `SupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `SupplyIntervalOperations` |
| `SupplyCorrespondence` | [`certificates/SupplyCorrespondence.v`](../../../../../../../shared/certificates/SupplyCorrespondence.v) | `ImportedSupply` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `IbfTaskHelpers` | [`certificates/IbfTaskHelpers.v`](../../../../../../../shared/certificates/IbfTaskHelpers.v) | `ImportedIbfSupplyTask` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `IbfSupplyTaskCorrespondence` | [`certificates/IbfSupplyTaskCorrespondence.v`](../../../../../../../shared/certificates/IbfSupplyTaskCorrespondence.v) | `ImportedIbfSupplyTask` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `IbfTaskFullHelpers` | [`certificates/IbfTaskFullHelpers.v`](../../../../../../../shared/certificates/IbfTaskFullHelpers.v) | `ImportedAbstractSeqRta` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ServiceInversionPredCorrespondence` | [`certificates/ServiceInversionPredCorrespondence.v`](../../../../../../../shared/certificates/ServiceInversionPredCorrespondence.v) | `ImportedServiceInversionPred` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `InterferenceCorrespondence` | [`certificates/InterferenceCorrespondence.v`](../../../../../../../shared/certificates/InterferenceCorrespondence.v) | `ImportedInterference` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `RsIwHelpers` | [`certificates/RsIwHelpers.v`](../../../../../../../shared/certificates/RsIwHelpers.v) | `ImportedFifoAhepBound` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `WorkloadBoundedCorrespondence` | [`certificates/WorkloadBoundedCorrespondence.v`](../../../../../../../shared/certificates/WorkloadBoundedCorrespondence.v) | `ImportedWorkloadBounded` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ServiceInversionBusyPrefixCorrespondence` | [`certificates/ServiceInversionBusyPrefixCorrespondence.v`](../../../../../../../shared/certificates/ServiceInversionBusyPrefixCorrespondence.v) | `ImportedServiceInversionBusyPrefix` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `ArrivalSequenceCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `BusyIntervalClassicalHelpers` | [`certificates/BusyIntervalClassicalHelpers.v`](../../../../../../../shared/certificates/BusyIntervalClassicalHelpers.v) | `ImportedSbfBusy` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `PredHelpers` | [`certificates/PredHelpers.v`](../../../../../../../shared/certificates/PredHelpers.v) | `ImportedSbfBusy` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `SbfBusyCorrespondence` | [`certificates/SbfBusyCorrespondence.v`](../../../../../../../shared/certificates/SbfBusyCorrespondence.v) | `ImportedSbfBusy` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `PreemptionTimeCorrespondence` | [`certificates/PreemptionTimeCorrespondence.v`](../../../../../../../shared/certificates/PreemptionTimeCorrespondence.v) | `ImportedPreemptionTime` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `PriorityDrivenCorrespondence` | [`certificates/PriorityDrivenCorrespondence.v`](../../../../../../../shared/certificates/PriorityDrivenCorrespondence.v) | `ImportedPriorityDriven` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `PcoBaseAdapter` | [`certificates/PriorityBaseAdapter.v`](../../../../../../../shared/certificates/PriorityBaseAdapter.v) | `ImportedPriorityDefinitions` → `ImportedRtaPrmEdfFullyNonpreemptive`; module named `PcoBaseAdapter` |
| `EdfAthepBoundCorrespondence` | [`certificates/EdfAthepBoundCorrespondence.v`](../../../../../../../shared/certificates/EdfAthepBoundCorrespondence.v) | `ImportedEdfAthepBound` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `BlockingBoundEdfCorrespondence` | [`certificates/BlockingBoundEdfCorrespondence.v`](../../../../../../../shared/certificates/BlockingBoundEdfCorrespondence.v) | `ImportedBlockingBoundEdf` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `SearchSpaceEdfCorrespondence` | [`certificates/SearchSpaceEdfCorrespondence.v`](../../../../../../../shared/certificates/SearchSpaceEdfCorrespondence.v) | `ImportedRtaArmEdfFloatingNonpreemptive` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `EdfPiBoundCorrespondence` | [`certificates/EdfPiBoundCorrespondence.v`](../../../../../../../shared/certificates/EdfPiBoundCorrespondence.v) | `ImportedEdfPiBound` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `PredCorrespondence` | [`certificates/PredCorrespondence.v`](../../../../../../../shared/certificates/PredCorrespondence.v) | `ImportedPred` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `PlainCorrespondence` | [`certificates/PlainCorrespondence.v`](../../../../../../../shared/certificates/PlainCorrespondence.v) | `ImportedPlain` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence.v`](../../../../../../../shared/certificates/NatSubCorrespondence.v) | `ImportedNat` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `DivModCorrespondence` | [`certificates/DivModCorrespondence.v`](../../../../../../../shared/certificates/DivModCorrespondence.v) | `ImportedDivMod ImportedNat` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `PeriodicCorrespondence` | [`certificates/PeriodicCorrespondence.v`](../../../../../../../shared/certificates/PeriodicCorrespondence.v) | `ImportedPeriodic` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `FsScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyNonpreemptive`; module named `FsScheduleBaseAdapter` |
| `FsScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `FsScheduleFiniteOperations` |
| `FsScheduleCorrespondence` | [`certificates/FsScheduleCorrespondence.v`](../../../../../../../shared/certificates/FsScheduleCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `FsProcessorStateCorrespondence` | [`certificates/ScheduleProcessorStateCorrespondence.v`](../../../../../../../shared/certificates/ScheduleProcessorStateCorrespondence.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyNonpreemptive`; certificate module names in `Require` lines renamed; module named `FsProcessorStateCorrespondence` |
| `FactsSupplyPlatformPropertiesCorrespondence` | [`certificates/FactsSupplyPlatformPropertiesCorrespondence.v`](../../../../../../../shared/certificates/FactsSupplyPlatformPropertiesCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedRtaPrmEdfFullyNonpreemptive` |
| `RsPStateCover` | [`certificates/RsPStateCover.v`](../../../../../../../shared/certificates/RsPStateCover.v) | `edRtaArmEdfFloatingNonpreemptive` → `edRtaPrmEdfFullyNonpreemptive` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `ServiceInversionPredComputationInterface` | [`lean_interfaces/ServiceInversionPredComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ServiceInversionPredComputationInterface.lean) |
| `AbstractDefinitionsComputationInterface` | [`lean_interfaces/AbstractDefinitionsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/AbstractDefinitionsComputationInterface.lean) |
| `BusyPrefixComputationInterface` | [`lean_interfaces/BusyPrefixComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BusyPrefixComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `WorkloadComputationInterface` | [`lean_interfaces/WorkloadComputationInterface.lean`](../../../../../../../shared/lean_interfaces/WorkloadComputationInterface.lean) |
| `BusyIntervalAbstractComputationInterface` | [`lean_interfaces/BusyIntervalAbstractComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BusyIntervalAbstractComputationInterface.lean) |
| `LowerBoundOnServiceComputationInterface` | [`lean_interfaces/LowerBoundOnServiceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/LowerBoundOnServiceComputationInterface.lean) |
| `TaskPreemptionParametersComputationInterface` | [`lean_interfaces/TaskPreemptionParametersComputationInterface.lean`](../../../../../../../shared/lean_interfaces/TaskPreemptionParametersComputationInterface.lean) |
| `AbstractRtaComputationInterface` | [`lean_interfaces/AbstractRtaComputationInterface.lean`](../../../../../../../shared/lean_interfaces/AbstractRtaComputationInterface.lean) |
| `IdealAbstractRtaComputationInterface` | [`lean_interfaces/IdealAbstractRtaComputationInterface.lean`](../../../../../../../shared/lean_interfaces/IdealAbstractRtaComputationInterface.lean) |
| `RequestBoundFunctionComputationInterface` | [`lean_interfaces/RequestBoundFunctionComputationInterface.lean`](../../../../../../../shared/lean_interfaces/RequestBoundFunctionComputationInterface.lean) |
| `TaskScheduleComputationInterface` | [`lean_interfaces/TaskScheduleComputationInterface.lean`](../../../../../../../shared/lean_interfaces/TaskScheduleComputationInterface.lean) |
| `SequentialityComputationInterface` | [`lean_interfaces/SequentialityComputationInterface.lean`](../../../../../../../shared/lean_interfaces/SequentialityComputationInterface.lean) |
| `ServiceOfJobsComputationInterface` | [`lean_interfaces/ServiceOfJobsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ServiceOfJobsComputationInterface.lean) |
| `CurvesComputationInterface` | [`lean_interfaces/CurvesComputationInterface.lean`](../../../../../../../shared/lean_interfaces/CurvesComputationInterface.lean) |
| `IbfTaskComputationInterface` | [`lean_interfaces/IbfTaskComputationInterface.lean`](../../../../../../../shared/lean_interfaces/IbfTaskComputationInterface.lean) |
| `SupplyComputationInterface` | [`lean_interfaces/SupplyComputationInterface.lean`](../../../../../../../shared/lean_interfaces/SupplyComputationInterface.lean) |
| `IbfSupplyComputationInterface` | [`lean_interfaces/IbfSupplyComputationInterface.lean`](../../../../../../../shared/lean_interfaces/IbfSupplyComputationInterface.lean) |
| `IbfSupplyTaskComputationInterface` | [`lean_interfaces/IbfSupplyTaskComputationInterface.lean`](../../../../../../../shared/lean_interfaces/IbfSupplyTaskComputationInterface.lean) |
| `PreemptionTimeComputationInterface` | [`lean_interfaces/PreemptionTimeComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PreemptionTimeComputationInterface.lean) |
| `PriorityDrivenComputationInterface` | [`lean_interfaces/PriorityDrivenComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PriorityDrivenComputationInterface.lean) |
| `ScheduledComputationInterface` | [`lean_interfaces/ScheduledComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduledComputationInterface.lean) |
| `ProcessorStateCoverInterface` | [`lean_interfaces/ProcessorStateCoverInterface.lean`](../../../../../../../shared/lean_interfaces/ProcessorStateCoverInterface.lean) |
| `FactsPreemptionComputationInterface` | [`lean_interfaces/FactsPreemptionComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsPreemptionComputationInterface.lean) |
| `BusyIntervalClassicalComputationInterface` | [`lean_interfaces/BusyIntervalClassicalComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BusyIntervalClassicalComputationInterface.lean) |
| `FactsServiceOfJobsComputationInterface` | [`lean_interfaces/FactsServiceOfJobsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsServiceOfJobsComputationInterface.lean) |
| `PriorityInversionComputationInterface` | [`lean_interfaces/PriorityInversionComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PriorityInversionComputationInterface.lean) |
| `WorkBearingReadinessComputationInterface` | [`lean_interfaces/WorkBearingReadinessComputationInterface.lean`](../../../../../../../shared/lean_interfaces/WorkBearingReadinessComputationInterface.lean) |
| `JobPropertiesExportInterface` | [`lean_interfaces/JobPropertiesExportInterface.lean`](../../../../../../../shared/lean_interfaces/JobPropertiesExportInterface.lean) |
| `ExistenceComputationInterface` | [`lean_interfaces/ExistenceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ExistenceComputationInterface.lean) |
| `HepAtPtComputationInterface` | [`lean_interfaces/HepAtPtComputationInterface.lean`](../../../../../../../shared/lean_interfaces/HepAtPtComputationInterface.lean) |
| `PiComputationInterface` | [`lean_interfaces/PiComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PiComputationInterface.lean) |
| `PiBoundComputationInterface` | [`lean_interfaces/PiBoundComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PiBoundComputationInterface.lean) |
| `ServiceInversionBusyPrefixComputationInterface` | [`lean_interfaces/ServiceInversionBusyPrefixComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ServiceInversionBusyPrefixComputationInterface.lean) |
| `BusyIntervalServiceInversionComputationInterface` | [`lean_interfaces/BusyIntervalServiceInversionComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BusyIntervalServiceInversionComputationInterface.lean) |
| `InterferenceComputationInterface` | [`lean_interfaces/InterferenceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/InterferenceComputationInterface.lean) |
| `FactsInterferenceComputationInterface` | [`lean_interfaces/FactsInterferenceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsInterferenceComputationInterface.lean) |
| `RsIwInstantiationComputationInterface` | [`lean_interfaces/RsIwInstantiationComputationInterface.lean`](../../../../../../../shared/lean_interfaces/RsIwInstantiationComputationInterface.lean) |
| `WorkloadBoundedComputationInterface` | [`lean_interfaces/WorkloadBoundedComputationInterface.lean`](../../../../../../../shared/lean_interfaces/WorkloadBoundedComputationInterface.lean) |
| `TaskIntraInterferenceBoundComputationInterface` | [`lean_interfaces/TaskIntraInterferenceBoundComputationInterface.lean`](../../../../../../../shared/lean_interfaces/TaskIntraInterferenceBoundComputationInterface.lean) |
| `PredExportInterface` | [`lean_interfaces/PredExportInterface.lean`](../../../../../../../shared/lean_interfaces/PredExportInterface.lean) |
| `SbfBusyComputationInterface` | [`lean_interfaces/SbfBusyComputationInterface.lean`](../../../../../../../shared/lean_interfaces/SbfBusyComputationInterface.lean) |
| `BoundedBiJlfpComputationInterface` | [`lean_interfaces/BoundedBiJlfpComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BoundedBiJlfpComputationInterface.lean) |
| `BlockingBoundEdfComputationInterface` | [`lean_interfaces/BlockingBoundEdfComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BlockingBoundEdfComputationInterface.lean) |
| `EdfAthepBoundComputationInterface` | [`lean_interfaces/EdfAthepBoundComputationInterface.lean`](../../../../../../../shared/lean_interfaces/EdfAthepBoundComputationInterface.lean) |
| `FactsSearchSpaceEdfComputationInterface` | [`lean_interfaces/FactsSearchSpaceEdfComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsSearchSpaceEdfComputationInterface.lean) |
| `EdfPiBoundComputationInterface` | [`lean_interfaces/EdfPiBoundComputationInterface.lean`](../../../../../../../shared/lean_interfaces/EdfPiBoundComputationInterface.lean) |
| `PlatformPropertiesComputationInterface` | [`lean_interfaces/PlatformPropertiesComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PlatformPropertiesComputationInterface.lean) |
| `DivModComputationInterface` | [`lean_interfaces/DivModComputationInterface.lean`](../../../../../../../shared/lean_interfaces/DivModComputationInterface.lean) |
| `FactsSbfPeriodicComputationInterface` | [`lean_interfaces/FactsSbfPeriodicComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsSbfPeriodicComputationInterface.lean) |
