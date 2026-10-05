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
| `OvhArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedOverheadsScheduleChangeBound`; module named `OvhArrivalsSeqBaseAdapter` |
| `OvhArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhArrivalsSeqOperations` |
| `OvhArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhArrivalsSeqCorrespondence` |
| `OvhArrivalsCorrespondence` | [`certificates/OvhArrivalsCorrespondence.v`](../../../../../../../shared/certificates/OvhArrivalsCorrespondence.v) | `ImportedOverheadsSchedule` → `ImportedOverheadsScheduleChangeBound` |
| `OvhJitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedOverheadsScheduleChangeBound`; module named `OvhJitterSvcBaseAdapter` |
| `OvhJitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhJitterSvcNatBoolOperations` |
| `OvhJitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhJitterSvcIntervalOperations` |
| `OvhJitterSvcScheduleOperations` | [`certificates/OvhJitterSvcScheduleOperations.v`](../../../../../../../shared/certificates/OvhJitterSvcScheduleOperations.v) | `ImportedOverheadsSchedule` → `ImportedOverheadsScheduleChangeBound` |
| `OvhJitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhJitterSvcJobOperations` |
| `OvhPreemptionParameterCorrespondence` | [`certificates/ExcPreemptionParameterCorrespondence.v`](../../../../../../../shared/certificates/ExcPreemptionParameterCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhPreemptionParameterCorrespondence` |
| `OvhPreemptionTimeCorrespondence` | [`certificates/ExcPreemptionTimeCorrespondence.v`](../../../../../../../shared/certificates/ExcPreemptionTimeCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhPreemptionTimeCorrespondence` |
| `OvhPriorityDrivenCorrespondence` | [`certificates/ExcPriorityDrivenCorrespondence.v`](../../../../../../../shared/certificates/ExcPriorityDrivenCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhPriorityDrivenCorrespondence` |
| `OvhPStateCoverHelpers` | [`certificates/ExcPStateCoverHelpers.v`](../../../../../../../shared/certificates/ExcPStateCoverHelpers.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhPStateCoverHelpers` |
| `OvhFactsPreemptionHelpers` | [`certificates/ExcFactsPreemptionHelpers.v`](../../../../../../../shared/certificates/ExcFactsPreemptionHelpers.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhFactsPreemptionHelpers` |
| `OvhWorkloadCorrespondence` | [`certificates/WorkloadCorrespondence.v`](../../../../../../../shared/certificates/WorkloadCorrespondence.v) | `ImportedWorkload` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhWorkloadCorrespondence` |
| `OvhPriorityInversionCorrespondence` | [`certificates/ExcPriorityInversionCorrespondence.v`](../../../../../../../shared/certificates/ExcPriorityInversionCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhPriorityInversionCorrespondence` |
| `OvhExistenceHelpers` | [`certificates/ExcExistenceHelpers.v`](../../../../../../../shared/certificates/ExcExistenceHelpers.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhExistenceHelpers` |
| `OvhHepAtPtHelpers` | [`certificates/ExcHepAtPtHelpers.v`](../../../../../../../shared/certificates/ExcHepAtPtHelpers.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhHepAtPtHelpers` |
| `OvhTaskPreemptionParametersCorrespondence` | [`certificates/ExcTaskPreemptionParametersCorrespondence.v`](../../../../../../../shared/certificates/ExcTaskPreemptionParametersCorrespondence.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhTaskPreemptionParametersCorrespondence` |
| `OvhBusyIntervalPiHelpers` | [`certificates/ExcBusyIntervalPiHelpers.v`](../../../../../../../shared/certificates/ExcBusyIntervalPiHelpers.v) | `ImportedExceedanceSbf` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhBusyIntervalPiHelpers` |
| `OvhStateRel` | [`certificates/OvhStateRel.v`](../../../../../../../shared/certificates/OvhStateRel.v) | `ImportedOverheadsSchedule` → `ImportedOverheadsScheduleChangeBound` |
| `OvhCurvesCorrespondence` | [`certificates/CurvesCorrespondence.v`](../../../../../../../shared/certificates/CurvesCorrespondence.v) | `ImportedCurves` → `ImportedOverheadsScheduleChangeBound`; certificate module names in `Require` lines renamed; module named `OvhCurvesCorrespondence` |
| `ScheduleChangeBaseAdapter` | [`certificates/ScheduleChangeBaseAdapter.v`](../../../../../../../shared/certificates/ScheduleChangeBaseAdapter.v) | `ImportedScheduleChange` → `ImportedOverheadsScheduleChangeBound` |
| `ScheduleChangeStateAdapter` | [`certificates/ScheduleChangeStateAdapter.v`](../../../../../../../shared/certificates/ScheduleChangeStateAdapter.v) | `ImportedScheduleChange` → `ImportedOverheadsScheduleChangeBound` |
| `ScheduleChangeOptionOperations` | [`certificates/ScheduleChangeOptionOperations.v`](../../../../../../../shared/certificates/ScheduleChangeOptionOperations.v) | `ImportedScheduleChange` → `ImportedOverheadsScheduleChangeBound` |
| `ScheduleChangeIntervalOperations` | [`certificates/ScheduleChangeIntervalOperations.v`](../../../../../../../shared/certificates/ScheduleChangeIntervalOperations.v) | `ImportedScheduleChange` → `ImportedOverheadsScheduleChangeBound` |
| `ScheduleChangeListOperations` | [`certificates/ScheduleChangeListOperations.v`](../../../../../../../shared/certificates/ScheduleChangeListOperations.v) | `ImportedScheduleChange` → `ImportedOverheadsScheduleChangeBound` |
| `ScheduleChangeCorrespondence` | [`certificates/ScheduleChangeCorrespondence.v`](../../../../../../../shared/certificates/ScheduleChangeCorrespondence.v) | `ImportedScheduleChange` → `ImportedOverheadsScheduleChangeBound` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
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
