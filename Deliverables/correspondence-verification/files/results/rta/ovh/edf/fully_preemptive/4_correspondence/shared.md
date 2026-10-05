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
| `OvhArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedRtaOvhEdfFullyPreemptive`; module named `OvhArrivalsSeqBaseAdapter` |
| `OvhArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhArrivalsSeqOperations` |
| `OvhArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhArrivalsSeqCorrespondence` |
| `OvhArrivalsCorrespondence` | [`certificates/OvhArrivalsCorrespondence.v`](../../../../../../../shared/certificates/OvhArrivalsCorrespondence.v) | `ImportedOverheadsSchedule` → `ImportedRtaOvhEdfFullyPreemptive` |
| `OvhJitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedRtaOvhEdfFullyPreemptive`; module named `OvhJitterSvcBaseAdapter` |
| `OvhJitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhJitterSvcNatBoolOperations` |
| `OvhJitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhJitterSvcIntervalOperations` |
| `OvhJitterSvcScheduleOperations` | [`certificates/OvhJitterSvcScheduleOperations.v`](../../../../../../../shared/certificates/OvhJitterSvcScheduleOperations.v) | `ImportedOverheadsSchedule` → `ImportedRtaOvhEdfFullyPreemptive` |
| `OvhJitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhJitterSvcJobOperations` |
| `OvhPreemptionParameterCorrespondence` | [`certificates/ExcPreemptionParameterCorrespondence.v`](../../../../../../../shared/certificates/ExcPreemptionParameterCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhPreemptionParameterCorrespondence` |
| `OvhPreemptionTimeCorrespondence` | [`certificates/ExcPreemptionTimeCorrespondence.v`](../../../../../../../shared/certificates/ExcPreemptionTimeCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhPreemptionTimeCorrespondence` |
| `OvhPriorityDrivenCorrespondence` | [`certificates/ExcPriorityDrivenCorrespondence.v`](../../../../../../../shared/certificates/ExcPriorityDrivenCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhPriorityDrivenCorrespondence` |
| `OvhPStateCoverHelpers` | [`certificates/ExcPStateCoverHelpers.v`](../../../../../../../shared/certificates/ExcPStateCoverHelpers.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhPStateCoverHelpers` |
| `OvhFactsPreemptionHelpers` | [`certificates/ExcFactsPreemptionHelpers.v`](../../../../../../../shared/certificates/ExcFactsPreemptionHelpers.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhFactsPreemptionHelpers` |
| `OvhWorkloadCorrespondence` | [`certificates/WorkloadCorrespondence.v`](../../../../../../../shared/certificates/WorkloadCorrespondence.v) | `ImportedWorkload` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhWorkloadCorrespondence` |
| `OvhPriorityInversionCorrespondence` | [`certificates/ExcPriorityInversionCorrespondence.v`](../../../../../../../shared/certificates/ExcPriorityInversionCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhPriorityInversionCorrespondence` |
| `OvhExistenceHelpers` | [`certificates/ExcExistenceHelpers.v`](../../../../../../../shared/certificates/ExcExistenceHelpers.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhExistenceHelpers` |
| `OvhHepAtPtHelpers` | [`certificates/ExcHepAtPtHelpers.v`](../../../../../../../shared/certificates/ExcHepAtPtHelpers.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhHepAtPtHelpers` |
| `OvhTaskPreemptionParametersCorrespondence` | [`certificates/ExcTaskPreemptionParametersCorrespondence.v`](../../../../../../../shared/certificates/ExcTaskPreemptionParametersCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhTaskPreemptionParametersCorrespondence` |
| `OvhBusyIntervalPiHelpers` | [`certificates/ExcBusyIntervalPiHelpers.v`](../../../../../../../shared/certificates/ExcBusyIntervalPiHelpers.v) | `ImportedExceedanceSbf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhBusyIntervalPiHelpers` |
| `OvhStateRel` | [`certificates/OvhStateRel.v`](../../../../../../../shared/certificates/OvhStateRel.v) | `ImportedOverheadsSchedule` → `ImportedRtaOvhEdfFullyPreemptive` |
| `OvhCurvesCorrespondence` | [`certificates/CurvesCorrespondence.v`](../../../../../../../shared/certificates/CurvesCorrespondence.v) | `ImportedCurves` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhCurvesCorrespondence` |
| `OvhRequestBoundFunctionCorrespondence` | [`certificates/RequestBoundFunctionCorrespondence.v`](../../../../../../../shared/certificates/RequestBoundFunctionCorrespondence.v) | `ImportedRequestBoundFunction` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhRequestBoundFunctionCorrespondence` |
| `OvhEdfAthepBoundCorrespondence` | [`certificates/EdfAthepBoundCorrespondence.v`](../../../../../../../shared/certificates/EdfAthepBoundCorrespondence.v) | `ImportedEdfAthepBound` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhEdfAthepBoundCorrespondence` |
| `OvhBlockingBoundEdfCorrespondence` | [`certificates/BlockingBoundEdfCorrespondence.v`](../../../../../../../shared/certificates/BlockingBoundEdfCorrespondence.v) | `ImportedBlockingBoundEdf` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OvhBlockingBoundEdfCorrespondence` |
| `OvhSearchSpaceEdfCorrespondence` | [`certificates/OvhSearchSpaceEdfCorrespondence.v`](../../../../../../../shared/certificates/OvhSearchSpaceEdfCorrespondence.v) | `ImportedRtaOvhEdfFloatingNonpreemptive` → `ImportedRtaOvhEdfFullyPreemptive` |
| `ScheduleChangeBaseAdapter` | [`certificates/ScheduleChangeBaseAdapter.v`](../../../../../../../shared/certificates/ScheduleChangeBaseAdapter.v) | `ImportedScheduleChange` → `ImportedRtaOvhEdfFullyPreemptive` |
| `ScheduleChangeStateAdapter` | [`certificates/ScheduleChangeStateAdapter.v`](../../../../../../../shared/certificates/ScheduleChangeStateAdapter.v) | `ImportedScheduleChange` → `ImportedRtaOvhEdfFullyPreemptive` |
| `ScheduleChangeOptionOperations` | [`certificates/ScheduleChangeOptionOperations.v`](../../../../../../../shared/certificates/ScheduleChangeOptionOperations.v) | `ImportedScheduleChange` → `ImportedRtaOvhEdfFullyPreemptive` |
| `ScheduleChangeIntervalOperations` | [`certificates/ScheduleChangeIntervalOperations.v`](../../../../../../../shared/certificates/ScheduleChangeIntervalOperations.v) | `ImportedScheduleChange` → `ImportedRtaOvhEdfFullyPreemptive` |
| `ScheduleChangeListOperations` | [`certificates/ScheduleChangeListOperations.v`](../../../../../../../shared/certificates/ScheduleChangeListOperations.v) | `ImportedScheduleChange` → `ImportedRtaOvhEdfFullyPreemptive` |
| `ScheduleChangeCorrespondence` | [`certificates/ScheduleChangeCorrespondence.v`](../../../../../../../shared/certificates/ScheduleChangeCorrespondence.v) | `ImportedScheduleChange` → `ImportedRtaOvhEdfFullyPreemptive` |
| `OverheadsBaseAdapter` | [`certificates/OverheadsBaseAdapter.v`](../../../../../../../shared/certificates/OverheadsBaseAdapter.v) | `ImportedOverheads` → `ImportedRtaOvhEdfFullyPreemptive` |
| `OverheadsNatBoolOperations` | [`certificates/OverheadsNatBoolOperations.v`](../../../../../../../shared/certificates/OverheadsNatBoolOperations.v) | `ImportedOverheads` → `ImportedRtaOvhEdfFullyPreemptive` |
| `OverheadsIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed; module named `OverheadsIntervalOperations` |
| `OverheadsCorrespondence` | [`certificates/OverheadsCorrespondence.v`](../../../../../../../shared/certificates/OverheadsCorrespondence.v) | `ImportedOverheadResourceModel` → `ImportedRtaOvhEdfFullyPreemptive` |
| `OverheadResourceModelCorrespondence` | [`certificates/OverheadResourceModelCorrespondence.v`](../../../../../../../shared/certificates/OverheadResourceModelCorrespondence.v) | `ImportedOverheadResourceModel` → `ImportedRtaOvhEdfFullyPreemptive`; certificate module names in `Require` lines renamed |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `PreemptionTimeComputationInterface` | [`lean_interfaces/PreemptionTimeComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PreemptionTimeComputationInterface.lean) |
| `PriorityDrivenComputationInterface` | [`lean_interfaces/PriorityDrivenComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PriorityDrivenComputationInterface.lean) |
| `ScheduledComputationInterface` | [`lean_interfaces/ScheduledComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduledComputationInterface.lean) |
| `ProcessorStateCoverInterface` | [`lean_interfaces/ProcessorStateCoverInterface.lean`](../../../../../../../shared/lean_interfaces/ProcessorStateCoverInterface.lean) |
| `FactsPreemptionComputationInterface` | [`lean_interfaces/FactsPreemptionComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsPreemptionComputationInterface.lean) |
| `BusyIntervalClassicalComputationInterface` | [`lean_interfaces/BusyIntervalClassicalComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BusyIntervalClassicalComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `WorkloadComputationInterface` | [`lean_interfaces/WorkloadComputationInterface.lean`](../../../../../../../shared/lean_interfaces/WorkloadComputationInterface.lean) |
| `ServiceOfJobsComputationInterface` | [`lean_interfaces/ServiceOfJobsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ServiceOfJobsComputationInterface.lean) |
| `FactsServiceOfJobsComputationInterface` | [`lean_interfaces/FactsServiceOfJobsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsServiceOfJobsComputationInterface.lean) |
| `PriorityInversionComputationInterface` | [`lean_interfaces/PriorityInversionComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PriorityInversionComputationInterface.lean) |
| `WorkBearingReadinessComputationInterface` | [`lean_interfaces/WorkBearingReadinessComputationInterface.lean`](../../../../../../../shared/lean_interfaces/WorkBearingReadinessComputationInterface.lean) |
| `JobPropertiesExportInterface` | [`lean_interfaces/JobPropertiesExportInterface.lean`](../../../../../../../shared/lean_interfaces/JobPropertiesExportInterface.lean) |
| `ExistenceComputationInterface` | [`lean_interfaces/ExistenceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ExistenceComputationInterface.lean) |
| `HepAtPtComputationInterface` | [`lean_interfaces/HepAtPtComputationInterface.lean`](../../../../../../../shared/lean_interfaces/HepAtPtComputationInterface.lean) |
| `TaskPreemptionParametersComputationInterface` | [`lean_interfaces/TaskPreemptionParametersComputationInterface.lean`](../../../../../../../shared/lean_interfaces/TaskPreemptionParametersComputationInterface.lean) |
| `PiComputationInterface` | [`lean_interfaces/PiComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PiComputationInterface.lean) |
| `OverheadsScheduleComputationInterface` | [`lean_interfaces/OverheadsScheduleComputationInterface.lean`](../../../../../../../shared/lean_interfaces/OverheadsScheduleComputationInterface.lean) |
| `OverheadsInstWitnessComputationInterface` | [`lean_interfaces/OverheadsInstWitnessComputationInterface.lean`](../../../../../../../shared/lean_interfaces/OverheadsInstWitnessComputationInterface.lean) |
| `OverheadsInstWitness2ComputationInterface` | [`lean_interfaces/OverheadsInstWitness2ComputationInterface.lean`](../../../../../../../shared/lean_interfaces/OverheadsInstWitness2ComputationInterface.lean) |
| `PriorityBumpFactsComputationInterface` | [`lean_interfaces/PriorityBumpFactsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/PriorityBumpFactsComputationInterface.lean) |
| `ScheduleChangeComputationInterface` | [`lean_interfaces/ScheduleChangeComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduleChangeComputationInterface.lean) |
| `FactsArrivalCurvesComputationInterface` | [`lean_interfaces/FactsArrivalCurvesComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsArrivalCurvesComputationInterface.lean) |
| `ScheduleChangeBoundComputationInterface` | [`lean_interfaces/ScheduleChangeBoundComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduleChangeBoundComputationInterface.lean) |
| `ScheduleChangeFactsComputationInterface` | [`lean_interfaces/ScheduleChangeFactsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduleChangeFactsComputationInterface.lean) |
| `OverheadResourceModelComputationInterface` | [`lean_interfaces/OverheadResourceModelComputationInterface.lean`](../../../../../../../shared/lean_interfaces/OverheadResourceModelComputationInterface.lean) |
| `OverheadsComputationInterface` | [`lean_interfaces/OverheadsComputationInterface.lean`](../../../../../../../shared/lean_interfaces/OverheadsComputationInterface.lean) |
| `SupplyComputationInterface` | [`lean_interfaces/SupplyComputationInterface.lean`](../../../../../../../shared/lean_interfaces/SupplyComputationInterface.lean) |
| `BlackoutBoundComputationInterface` | [`lean_interfaces/BlackoutBoundComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BlackoutBoundComputationInterface.lean) |
| `PredExportInterface` | [`lean_interfaces/PredExportInterface.lean`](../../../../../../../shared/lean_interfaces/PredExportInterface.lean) |
| `SbfBusyComputationInterface` | [`lean_interfaces/SbfBusyComputationInterface.lean`](../../../../../../../shared/lean_interfaces/SbfBusyComputationInterface.lean) |
| `OverheadsSbfJlfpComputationInterface` | [`lean_interfaces/OverheadsSbfJlfpComputationInterface.lean`](../../../../../../../shared/lean_interfaces/OverheadsSbfJlfpComputationInterface.lean) |
| `WorkloadBoundedComputationInterface` | [`lean_interfaces/WorkloadBoundedComputationInterface.lean`](../../../../../../../shared/lean_interfaces/WorkloadBoundedComputationInterface.lean) |
| `RequestBoundFunctionComputationInterface` | [`lean_interfaces/RequestBoundFunctionComputationInterface.lean`](../../../../../../../shared/lean_interfaces/RequestBoundFunctionComputationInterface.lean) |
| `CurvesComputationInterface` | [`lean_interfaces/CurvesComputationInterface.lean`](../../../../../../../shared/lean_interfaces/CurvesComputationInterface.lean) |
| `EdfAthepBoundComputationInterface` | [`lean_interfaces/EdfAthepBoundComputationInterface.lean`](../../../../../../../shared/lean_interfaces/EdfAthepBoundComputationInterface.lean) |
| `BlockingBoundEdfComputationInterface` | [`lean_interfaces/BlockingBoundEdfComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BlockingBoundEdfComputationInterface.lean) |
| `FactsSearchSpaceEdfComputationInterface` | [`lean_interfaces/FactsSearchSpaceEdfComputationInterface.lean`](../../../../../../../shared/lean_interfaces/FactsSearchSpaceEdfComputationInterface.lean) |
