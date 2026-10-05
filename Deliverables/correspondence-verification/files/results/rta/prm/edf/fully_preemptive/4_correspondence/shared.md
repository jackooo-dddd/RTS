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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyPreemptive`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedRtaPrmEdfFullyPreemptive` |
| `WorkloadCorrespondence` | [`certificates/WorkloadCorrespondence.v`](../../../../../../../shared/certificates/WorkloadCorrespondence.v) | `ImportedWorkload` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractDefinitionsBaseAdapter` | [`certificates/AbstractDefinitionsBaseAdapter.v`](../../../../../../../shared/certificates/AbstractDefinitionsBaseAdapter.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ServiceBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ServiceNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `ServiceNatBoolOperations` |
| `AbstractDefinitionsArrivalOperations` | [`certificates/AbstractDefinitionsArrivalOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsArrivalOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractDefinitionsClasses` | [`certificates/AbstractDefinitionsClasses.v`](../../../../../../../shared/certificates/AbstractDefinitionsClasses.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractDefinitionsNatBoolOperations` | [`certificates/AbstractDefinitionsNatBoolOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsNatBoolOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractDefinitionsIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `AbstractDefinitionsIntervalOperations` |
| `AbstractDefinitionsOperations` | [`certificates/AbstractDefinitionsOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractDefinitionsSums` | [`certificates/AbstractDefinitionsSums.v`](../../../../../../../shared/certificates/AbstractDefinitionsSums.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractDefinitionsLogical` | [`certificates/AbstractDefinitionsLogical.v`](../../../../../../../shared/certificates/AbstractDefinitionsLogical.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ServiceIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ServiceScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractDefinitionsPendingOperations` | [`certificates/AbstractDefinitionsPendingOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsPendingOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractDefinitionsTaskOperations` | [`certificates/AbstractDefinitionsTaskOperations.v`](../../../../../../../shared/certificates/AbstractDefinitionsTaskOperations.v) | `ImportedAbstractDefinitions` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractDefinitionsBusyIntervalHelpers` | [`certificates/AbstractDefinitionsBusyIntervalHelpers.v`](../../../../../../../shared/certificates/AbstractDefinitionsBusyIntervalHelpers.v) | `ImportedBusyPrefix` → `ImportedRtaPrmEdfFullyPreemptive` |
| `AbstractRtaHelpers` | [`certificates/AbstractRtaHelpers.v`](../../../../../../../shared/certificates/AbstractRtaHelpers.v) | `ImportedIbfSupply` → `ImportedRtaPrmEdfFullyPreemptive` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedRtaPrmEdfFullyPreemptive`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `PreemptionParameterCorrespondence` | [`certificates/PreemptionParameterCorrespondence.v`](../../../../../../../shared/certificates/PreemptionParameterCorrespondence.v) | `ImportedPreemptionParameter` → `ImportedRtaPrmEdfFullyPreemptive` |
| `TaskPreemptionParametersCorrespondence` | [`certificates/TaskPreemptionParametersCorrespondence.v`](../../../../../../../shared/certificates/TaskPreemptionParametersCorrespondence.v) | `ImportedTaskPreemptionParameters` → `ImportedRtaPrmEdfFullyPreemptive` |
| `IdealAbstractRtaHelpers` | [`certificates/IdealAbstractRtaHelpers.v`](../../../../../../../shared/certificates/IdealAbstractRtaHelpers.v) | `ImportedIbfTask` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ArrivalSequenceBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ArrivalSequenceOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyPreemptive` |
| `TaskScheduleCorrespondence` | [`certificates/TaskScheduleCorrespondence.v`](../../../../../../../shared/certificates/TaskScheduleCorrespondence.v) | `ImportedTaskSchedule` → `ImportedRtaPrmEdfFullyPreemptive` |
| `CurvesCorrespondence` | [`certificates/CurvesCorrespondence.v`](../../../../../../../shared/certificates/CurvesCorrespondence.v) | `ImportedCurves` → `ImportedRtaPrmEdfFullyPreemptive` |
| `RequestBoundFunctionCorrespondence` | [`certificates/RequestBoundFunctionCorrespondence.v`](../../../../../../../shared/certificates/RequestBoundFunctionCorrespondence.v) | `ImportedRequestBoundFunction` → `ImportedRtaPrmEdfFullyPreemptive` |
| `SequentialityCorrespondence` | [`certificates/SequentialityCorrespondence.v`](../../../../../../../shared/certificates/SequentialityCorrespondence.v) | `ImportedSequentiality` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ServiceOfJobsCorrespondence` | [`certificates/ServiceOfJobsCorrespondence.v`](../../../../../../../shared/certificates/ServiceOfJobsCorrespondence.v) | `ImportedServiceOfJobs` → `ImportedRtaPrmEdfFullyPreemptive` |
| `SupplyScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyPreemptive`; module named `SupplyScheduleBaseAdapter` |
| `SupplyScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `SupplyScheduleFiniteOperations` |
| `SupplyScheduleOperations` | [`certificates/SupplyScheduleOperations.v`](../../../../../../../shared/certificates/SupplyScheduleOperations.v) | `ImportedSupply` → `ImportedRtaPrmEdfFullyPreemptive` |
| `SupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedRtaPrmEdfFullyPreemptive`; module named `SupplyBaseAdapter` |
| `SupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../../../shared/certificates/SupplyNatBoolOperations.v) | `ImportedSupply` → `ImportedRtaPrmEdfFullyPreemptive` |
| `SupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `SupplyIntervalOperations` |
| `SupplyCorrespondence` | [`certificates/SupplyCorrespondence.v`](../../../../../../../shared/certificates/SupplyCorrespondence.v) | `ImportedSupply` → `ImportedRtaPrmEdfFullyPreemptive` |
| `IbfTaskHelpers` | [`certificates/IbfTaskHelpers.v`](../../../../../../../shared/certificates/IbfTaskHelpers.v) | `ImportedIbfSupplyTask` → `ImportedRtaPrmEdfFullyPreemptive` |
| `IbfSupplyTaskCorrespondence` | [`certificates/IbfSupplyTaskCorrespondence.v`](../../../../../../../shared/certificates/IbfSupplyTaskCorrespondence.v) | `ImportedIbfSupplyTask` → `ImportedRtaPrmEdfFullyPreemptive` |
| `IbfTaskFullHelpers` | [`certificates/IbfTaskFullHelpers.v`](../../../../../../../shared/certificates/IbfTaskFullHelpers.v) | `ImportedAbstractSeqRta` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ServiceInversionPredCorrespondence` | [`certificates/ServiceInversionPredCorrespondence.v`](../../../../../../../shared/certificates/ServiceInversionPredCorrespondence.v) | `ImportedServiceInversionPred` → `ImportedRtaPrmEdfFullyPreemptive` |
| `InterferenceCorrespondence` | [`certificates/InterferenceCorrespondence.v`](../../../../../../../shared/certificates/InterferenceCorrespondence.v) | `ImportedInterference` → `ImportedRtaPrmEdfFullyPreemptive` |
| `RsIwHelpers` | [`certificates/RsIwHelpers.v`](../../../../../../../shared/certificates/RsIwHelpers.v) | `ImportedFifoAhepBound` → `ImportedRtaPrmEdfFullyPreemptive` |
| `WorkloadBoundedCorrespondence` | [`certificates/WorkloadBoundedCorrespondence.v`](../../../../../../../shared/certificates/WorkloadBoundedCorrespondence.v) | `ImportedWorkloadBounded` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ServiceInversionBusyPrefixCorrespondence` | [`certificates/ServiceInversionBusyPrefixCorrespondence.v`](../../../../../../../shared/certificates/ServiceInversionBusyPrefixCorrespondence.v) | `ImportedServiceInversionBusyPrefix` → `ImportedRtaPrmEdfFullyPreemptive` |
| `ArrivalSequenceCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedRtaPrmEdfFullyPreemptive` |
| `BusyIntervalClassicalHelpers` | [`certificates/BusyIntervalClassicalHelpers.v`](../../../../../../../shared/certificates/BusyIntervalClassicalHelpers.v) | `ImportedSbfBusy` → `ImportedRtaPrmEdfFullyPreemptive` |
| `PredHelpers` | [`certificates/PredHelpers.v`](../../../../../../../shared/certificates/PredHelpers.v) | `ImportedSbfBusy` → `ImportedRtaPrmEdfFullyPreemptive` |
| `SbfBusyCorrespondence` | [`certificates/SbfBusyCorrespondence.v`](../../../../../../../shared/certificates/SbfBusyCorrespondence.v) | `ImportedSbfBusy` → `ImportedRtaPrmEdfFullyPreemptive` |
| `PreemptionTimeCorrespondence` | [`certificates/PreemptionTimeCorrespondence.v`](../../../../../../../shared/certificates/PreemptionTimeCorrespondence.v) | `ImportedPreemptionTime` → `ImportedRtaPrmEdfFullyPreemptive` |
| `PriorityDrivenCorrespondence` | [`certificates/PriorityDrivenCorrespondence.v`](../../../../../../../shared/certificates/PriorityDrivenCorrespondence.v) | `ImportedPriorityDriven` → `ImportedRtaPrmEdfFullyPreemptive` |
| `PcoBaseAdapter` | [`certificates/PriorityBaseAdapter.v`](../../../../../../../shared/certificates/PriorityBaseAdapter.v) | `ImportedPriorityDefinitions` → `ImportedRtaPrmEdfFullyPreemptive`; module named `PcoBaseAdapter` |
| `EdfAthepBoundCorrespondence` | [`certificates/EdfAthepBoundCorrespondence.v`](../../../../../../../shared/certificates/EdfAthepBoundCorrespondence.v) | `ImportedEdfAthepBound` → `ImportedRtaPrmEdfFullyPreemptive` |
| `BlockingBoundEdfCorrespondence` | [`certificates/BlockingBoundEdfCorrespondence.v`](../../../../../../../shared/certificates/BlockingBoundEdfCorrespondence.v) | `ImportedBlockingBoundEdf` → `ImportedRtaPrmEdfFullyPreemptive` |
| `SearchSpaceEdfCorrespondence` | [`certificates/SearchSpaceEdfCorrespondence.v`](../../../../../../../shared/certificates/SearchSpaceEdfCorrespondence.v) | `ImportedRtaArmEdfFloatingNonpreemptive` → `ImportedRtaPrmEdfFullyPreemptive` |
| `PredCorrespondence` | [`certificates/PredCorrespondence.v`](../../../../../../../shared/certificates/PredCorrespondence.v) | `ImportedPred` → `ImportedRtaPrmEdfFullyPreemptive` |
| `PlainCorrespondence` | [`certificates/PlainCorrespondence.v`](../../../../../../../shared/certificates/PlainCorrespondence.v) | `ImportedPlain` → `ImportedRtaPrmEdfFullyPreemptive` |
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence.v`](../../../../../../../shared/certificates/NatSubCorrespondence.v) | `ImportedNat` → `ImportedRtaPrmEdfFullyPreemptive` |
| `DivModCorrespondence` | [`certificates/DivModCorrespondence.v`](../../../../../../../shared/certificates/DivModCorrespondence.v) | `ImportedDivMod ImportedNat` → `ImportedRtaPrmEdfFullyPreemptive` |
| `PeriodicCorrespondence` | [`certificates/PeriodicCorrespondence.v`](../../../../../../../shared/certificates/PeriodicCorrespondence.v) | `ImportedPeriodic` → `ImportedRtaPrmEdfFullyPreemptive` |
| `FsScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyPreemptive`; module named `FsScheduleBaseAdapter` |
| `FsScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `FsScheduleFiniteOperations` |
| `FsScheduleCorrespondence` | [`certificates/FsScheduleCorrespondence.v`](../../../../../../../shared/certificates/FsScheduleCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedRtaPrmEdfFullyPreemptive` |
| `FsProcessorStateCorrespondence` | [`certificates/ScheduleProcessorStateCorrespondence.v`](../../../../../../../shared/certificates/ScheduleProcessorStateCorrespondence.v) | `ImportedSchedule` → `ImportedRtaPrmEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `FsProcessorStateCorrespondence` |
| `FactsSupplyPlatformPropertiesCorrespondence` | [`certificates/FactsSupplyPlatformPropertiesCorrespondence.v`](../../../../../../../shared/certificates/FactsSupplyPlatformPropertiesCorrespondence.v) | `ImportedFactsBehaviorSupply` → `ImportedRtaPrmEdfFullyPreemptive` |
| `RsPStateCover` | [`certificates/RsPStateCover.v`](../../../../../../../shared/certificates/RsPStateCover.v) | `edRtaArmEdfFloatingNonpreemptive` → `edRtaPrmEdfFullyPreemptive` |

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
| `PlatformPropertiesComputationInterface` | [`lean_interfaces/PlatformPropertiesComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PlatformPropertiesComputationInterface.lean) |
| `DivModComputationInterface` | [`lean_interfaces/DivModComputationInterface.lean`](../../../../../../../shared/lean_interfaces/DivModComputationInterface.lean) |
| `FactsSbfPeriodicComputationInterface` | [`lean_interfaces/FactsSbfPeriodicComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsSbfPeriodicComputationInterface.lean) |
