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
| `IdlArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedIdealCumulativeBounds`; module named `IdlArrivalsSeqBaseAdapter` |
| `IdlArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlArrivalsSeqOperations` |
| `IdlArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlArrivalsSeqCorrespondence` |
| `IdlArrivalsCorrespondence` | [`certificates/IdlArrivalsCorrespondence.v`](../../../../../../shared/certificates/IdlArrivalsCorrespondence.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlWorkloadCorrespondence` | [`certificates/WorkloadCorrespondence.v`](../../../../../../shared/certificates/WorkloadCorrespondence.v) | `ImportedWorkload` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlWorkloadCorrespondence` |
| `IdlAbstractDefinitionsBaseAdapter` | [`certificates/AbstractDefinitionsBaseAdapter.v`](../../../../../../shared/certificates/AbstractDefinitionsBaseAdapter.v) | `ImportedAbstractDefinitions` → `ImportedIdealCumulativeBounds`; module named `IdlAbstractDefinitionsBaseAdapter` |
| `IdlServiceBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedIdealCumulativeBounds`; module named `IdlServiceBaseAdapter` |
| `IdlServiceNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlServiceNatBoolOperations` |
| `IdlAbstractDefinitionsArrivalOperations` | [`certificates/AbstractDefinitionsArrivalOperations.v`](../../../../../../shared/certificates/AbstractDefinitionsArrivalOperations.v) | `ImportedAbstractDefinitions` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlAbstractDefinitionsArrivalOperations` |
| `IdlAbstractDefinitionsClasses` | [`certificates/AbstractDefinitionsClasses.v`](../../../../../../shared/certificates/AbstractDefinitionsClasses.v) | `ImportedAbstractDefinitions` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlAbstractDefinitionsClasses` |
| `IdlAbstractDefinitionsNatBoolOperations` | [`certificates/AbstractDefinitionsNatBoolOperations.v`](../../../../../../shared/certificates/AbstractDefinitionsNatBoolOperations.v) | `ImportedAbstractDefinitions` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlAbstractDefinitionsNatBoolOperations` |
| `IdlAbstractDefinitionsIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlAbstractDefinitionsIntervalOperations` |
| `IdlAbstractDefinitionsOperations` | [`certificates/AbstractDefinitionsOperations.v`](../../../../../../shared/certificates/AbstractDefinitionsOperations.v) | `ImportedAbstractDefinitions` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlAbstractDefinitionsOperations` |
| `IdlAbstractDefinitionsSums` | [`certificates/AbstractDefinitionsSums.v`](../../../../../../shared/certificates/AbstractDefinitionsSums.v) | `ImportedAbstractDefinitions` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlAbstractDefinitionsSums` |
| `IdlAbstractDefinitionsLogical` | [`certificates/AbstractDefinitionsLogical.v`](../../../../../../shared/certificates/AbstractDefinitionsLogical.v) | `ImportedAbstractDefinitions` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlAbstractDefinitionsLogical` |
| `IdlServiceIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlServiceIntervalOperations` |
| `IdlServiceScheduleOperations` | [`certificates/ExcJitterSvcScheduleOperations.v`](../../../../../../shared/certificates/ExcJitterSvcScheduleOperations.v) | `ImportedExceedanceSbf` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlServiceScheduleOperations` |
| `IdlAbstractDefinitionsPendingOperations` | [`certificates/IdlAbstractDefinitionsPendingOperations.v`](../../../../../../shared/certificates/IdlAbstractDefinitionsPendingOperations.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlAbstractDefinitionsTaskOperations` | [`certificates/AbstractDefinitionsTaskOperations.v`](../../../../../../shared/certificates/AbstractDefinitionsTaskOperations.v) | `ImportedAbstractDefinitions` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlAbstractDefinitionsTaskOperations` |
| `IdlAbstractDefinitionsBusyIntervalHelpers` | [`certificates/IdlAbstractDefinitionsBusyIntervalHelpers.v`](../../../../../../shared/certificates/IdlAbstractDefinitionsBusyIntervalHelpers.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlAbstractRtaHelpers` | [`certificates/IdlAbstractRtaHelpers.v`](../../../../../../shared/certificates/IdlAbstractRtaHelpers.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlJitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedIdealCumulativeBounds`; module named `IdlJitterSvcBaseAdapter` |
| `IdlJitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlJitterSvcNatBoolOperations` |
| `IdlJitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlJitterSvcIntervalOperations` |
| `IdlJitterSvcScheduleOperations` | [`certificates/ExcJitterSvcScheduleOperations.v`](../../../../../../shared/certificates/ExcJitterSvcScheduleOperations.v) | `ImportedExceedanceSbf` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlJitterSvcScheduleOperations` |
| `IdlJitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlJitterSvcJobOperations` |
| `IdlPreemptionParameterCorrespondence` | [`certificates/ExcPreemptionParameterCorrespondence.v`](../../../../../../shared/certificates/ExcPreemptionParameterCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlPreemptionParameterCorrespondence` |
| `IdlTaskPreemptionParametersCorrespondence` | [`certificates/ExcTaskPreemptionParametersCorrespondence.v`](../../../../../../shared/certificates/ExcTaskPreemptionParametersCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlTaskPreemptionParametersCorrespondence` |
| `IdlIdealAbstractRtaHelpers` | [`certificates/IdlIdealAbstractRtaHelpers.v`](../../../../../../shared/certificates/IdlIdealAbstractRtaHelpers.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlArrivalSequenceBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedIdealCumulativeBounds`; module named `IdlArrivalSequenceBaseAdapter` |
| `IdlArrivalSequenceOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlArrivalSequenceOperations` |
| `IdlTaskScheduleCorrespondence` | [`certificates/IdlTaskScheduleCorrespondence.v`](../../../../../../shared/certificates/IdlTaskScheduleCorrespondence.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlCurvesCorrespondence` | [`certificates/IdlCurvesCorrespondence.v`](../../../../../../shared/certificates/IdlCurvesCorrespondence.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlRequestBoundFunctionCorrespondence` | [`certificates/RequestBoundFunctionCorrespondence.v`](../../../../../../shared/certificates/RequestBoundFunctionCorrespondence.v) | `ImportedRequestBoundFunction` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlRequestBoundFunctionCorrespondence` |
| `IdlSequentialityCorrespondence` | [`certificates/IdlSequentialityCorrespondence.v`](../../../../../../shared/certificates/IdlSequentialityCorrespondence.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlServiceOfJobsCorrespondence` | [`certificates/IdlServiceOfJobsCorrespondence.v`](../../../../../../shared/certificates/IdlServiceOfJobsCorrespondence.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlSupplyScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedIdealCumulativeBounds`; module named `IdlSupplyScheduleBaseAdapter` |
| `IdlSupplyScheduleFiniteOperations` | [`certificates/IdlSupplyScheduleFiniteOperations.v`](../../../../../../shared/certificates/IdlSupplyScheduleFiniteOperations.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlSupplyScheduleOperations` | [`certificates/IdlSupplyScheduleOperations.v`](../../../../../../shared/certificates/IdlSupplyScheduleOperations.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlSupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedIdealCumulativeBounds`; module named `IdlSupplyBaseAdapter` |
| `IdlSupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../../shared/certificates/SupplyNatBoolOperations.v) | `ImportedSupply` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlSupplyNatBoolOperations` |
| `IdlSupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlSupplyIntervalOperations` |
| `IdlSupplyCorrespondence` | [`certificates/IdlSupplyCorrespondence.v`](../../../../../../shared/certificates/IdlSupplyCorrespondence.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlIbfTaskHelpers` | [`certificates/IdlIbfTaskHelpers.v`](../../../../../../shared/certificates/IdlIbfTaskHelpers.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlIbfSupplyTaskCorrespondence` | [`certificates/IdlIbfSupplyTaskCorrespondence.v`](../../../../../../shared/certificates/IdlIbfSupplyTaskCorrespondence.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlIbfTaskFullHelpers` | [`certificates/IdlIbfTaskFullHelpers.v`](../../../../../../shared/certificates/IdlIbfTaskFullHelpers.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlServiceInversionPredCorrespondence` | [`certificates/IdlServiceInversionPredCorrespondence.v`](../../../../../../shared/certificates/IdlServiceInversionPredCorrespondence.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlInterferenceCorrespondence` | [`certificates/IdlInterferenceCorrespondence.v`](../../../../../../shared/certificates/IdlInterferenceCorrespondence.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |
| `IdlPriorityInversionCorrespondence` | [`certificates/ExcPriorityInversionCorrespondence.v`](../../../../../../shared/certificates/ExcPriorityInversionCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedIdealCumulativeBounds`; certificate module names in `Require` lines renamed; module named `IdlPriorityInversionCorrespondence` |
| `IdlStateRel` | [`certificates/IdlStateRel.v`](../../../../../../shared/certificates/IdlStateRel.v) | `ImportedIdealIwInstantiation` → `ImportedIdealCumulativeBounds` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `ServiceInversionPredComputationInterface` | [`lean_interfaces/ServiceInversionPredComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceInversionPredComputationInterface.lean) |
| `AbstractDefinitionsComputationInterface` | [`lean_interfaces/AbstractDefinitionsComputationInterface.lean`](../../../../../../shared/lean_interfaces/AbstractDefinitionsComputationInterface.lean) |
| `BusyPrefixComputationInterface` | [`lean_interfaces/BusyPrefixComputationInterface.lean`](../../../../../../shared/lean_interfaces/BusyPrefixComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `WorkloadComputationInterface` | [`lean_interfaces/WorkloadComputationInterface.lean`](../../../../../../shared/lean_interfaces/WorkloadComputationInterface.lean) |
| `BusyIntervalAbstractComputationInterface` | [`lean_interfaces/BusyIntervalAbstractComputationInterface.lean`](../../../../../../shared/lean_interfaces/BusyIntervalAbstractComputationInterface.lean) |
| `LowerBoundOnServiceComputationInterface` | [`lean_interfaces/LowerBoundOnServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/LowerBoundOnServiceComputationInterface.lean) |
| `TaskPreemptionParametersComputationInterface` | [`lean_interfaces/TaskPreemptionParametersComputationInterface.lean`](../../../../../../shared/lean_interfaces/TaskPreemptionParametersComputationInterface.lean) |
| `AbstractRtaComputationInterface` | [`lean_interfaces/AbstractRtaComputationInterface.lean`](../../../../../../shared/lean_interfaces/AbstractRtaComputationInterface.lean) |
| `IdealAbstractRtaComputationInterface` | [`lean_interfaces/IdealAbstractRtaComputationInterface.lean`](../../../../../../shared/lean_interfaces/IdealAbstractRtaComputationInterface.lean) |
| `RequestBoundFunctionComputationInterface` | [`lean_interfaces/RequestBoundFunctionComputationInterface.lean`](../../../../../../shared/lean_interfaces/RequestBoundFunctionComputationInterface.lean) |
| `TaskScheduleComputationInterface` | [`lean_interfaces/TaskScheduleComputationInterface.lean`](../../../../../../shared/lean_interfaces/TaskScheduleComputationInterface.lean) |
| `SequentialityComputationInterface` | [`lean_interfaces/SequentialityComputationInterface.lean`](../../../../../../shared/lean_interfaces/SequentialityComputationInterface.lean) |
| `ServiceOfJobsComputationInterface` | [`lean_interfaces/ServiceOfJobsComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceOfJobsComputationInterface.lean) |
| `CurvesComputationInterface` | [`lean_interfaces/CurvesComputationInterface.lean`](../../../../../../shared/lean_interfaces/CurvesComputationInterface.lean) |
| `IbfTaskComputationInterface` | [`lean_interfaces/IbfTaskComputationInterface.lean`](../../../../../../shared/lean_interfaces/IbfTaskComputationInterface.lean) |
| `SupplyComputationInterface` | [`lean_interfaces/SupplyComputationInterface.lean`](../../../../../../shared/lean_interfaces/SupplyComputationInterface.lean) |
| `IbfSupplyComputationInterface` | [`lean_interfaces/IbfSupplyComputationInterface.lean`](../../../../../../shared/lean_interfaces/IbfSupplyComputationInterface.lean) |
| `IbfSupplyTaskComputationInterface` | [`lean_interfaces/IbfSupplyTaskComputationInterface.lean`](../../../../../../shared/lean_interfaces/IbfSupplyTaskComputationInterface.lean) |
| `PreemptionTimeComputationInterface` | [`lean_interfaces/PreemptionTimeComputationInterface.lean`](../../../../../../shared/lean_interfaces/PreemptionTimeComputationInterface.lean) |
| `PriorityDrivenComputationInterface` | [`lean_interfaces/PriorityDrivenComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityDrivenComputationInterface.lean) |
| `ScheduledComputationInterface` | [`lean_interfaces/ScheduledComputationInterface.lean`](../../../../../../shared/lean_interfaces/ScheduledComputationInterface.lean) |
| `ProcessorStateCoverInterface` | [`lean_interfaces/ProcessorStateCoverInterface.lean`](../../../../../../shared/lean_interfaces/ProcessorStateCoverInterface.lean) |
| `FactsPreemptionComputationInterface` | [`lean_interfaces/FactsPreemptionComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsPreemptionComputationInterface.lean) |
| `BusyIntervalClassicalComputationInterface` | [`lean_interfaces/BusyIntervalClassicalComputationInterface.lean`](../../../../../../shared/lean_interfaces/BusyIntervalClassicalComputationInterface.lean) |
| `FactsServiceOfJobsComputationInterface` | [`lean_interfaces/FactsServiceOfJobsComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsServiceOfJobsComputationInterface.lean) |
| `PriorityInversionComputationInterface` | [`lean_interfaces/PriorityInversionComputationInterface.lean`](../../../../../../shared/lean_interfaces/PriorityInversionComputationInterface.lean) |
| `WorkBearingReadinessComputationInterface` | [`lean_interfaces/WorkBearingReadinessComputationInterface.lean`](../../../../../../shared/lean_interfaces/WorkBearingReadinessComputationInterface.lean) |
| `JobPropertiesExportInterface` | [`lean_interfaces/JobPropertiesExportInterface.lean`](../../../../../../shared/lean_interfaces/JobPropertiesExportInterface.lean) |
| `ExistenceComputationInterface` | [`lean_interfaces/ExistenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ExistenceComputationInterface.lean) |
| `HepAtPtComputationInterface` | [`lean_interfaces/HepAtPtComputationInterface.lean`](../../../../../../shared/lean_interfaces/HepAtPtComputationInterface.lean) |
| `PiComputationInterface` | [`lean_interfaces/PiComputationInterface.lean`](../../../../../../shared/lean_interfaces/PiComputationInterface.lean) |
| `PiBoundComputationInterface` | [`lean_interfaces/PiBoundComputationInterface.lean`](../../../../../../shared/lean_interfaces/PiBoundComputationInterface.lean) |
| `ServiceInversionBusyPrefixComputationInterface` | [`lean_interfaces/ServiceInversionBusyPrefixComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceInversionBusyPrefixComputationInterface.lean) |
| `BusyIntervalServiceInversionComputationInterface` | [`lean_interfaces/BusyIntervalServiceInversionComputationInterface.lean`](../../../../../../shared/lean_interfaces/BusyIntervalServiceInversionComputationInterface.lean) |
| `InterferenceComputationInterface` | [`lean_interfaces/InterferenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/InterferenceComputationInterface.lean) |
| `FactsInterferenceComputationInterface` | [`lean_interfaces/FactsInterferenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsInterferenceComputationInterface.lean) |
| `RsIwInstantiationComputationInterface` | [`lean_interfaces/RsIwInstantiationComputationInterface.lean`](../../../../../../shared/lean_interfaces/RsIwInstantiationComputationInterface.lean) |
| `IdealScheduleComputationInterface` | [`lean_interfaces/IdealScheduleComputationInterface.lean`](../../../../../../shared/lean_interfaces/IdealScheduleComputationInterface.lean) |
| `IdealInstWitnessComputationInterface` | [`lean_interfaces/IdealInstWitnessComputationInterface.lean`](../../../../../../shared/lean_interfaces/IdealInstWitnessComputationInterface.lean) |
| `IdealIwInstantiationComputationInterface` | [`lean_interfaces/IdealIwInstantiationComputationInterface.lean`](../../../../../../shared/lean_interfaces/IdealIwInstantiationComputationInterface.lean) |
