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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedIbfSupply`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedIbfSupply`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedIbfSupply`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedIbfSupply` |
| `WorkloadCorrespondence` | [`certificates/WorkloadCorrespondence.v`](../../../../../../shared/certificates/WorkloadCorrespondence.v) | `ImportedWorkload` → `ImportedIbfSupply` |
| `AbstractDefinitionsBaseAdapter` | [`certificates/AbstractDefinitionsBaseAdapter.v`](../../../../../../shared/certificates/AbstractDefinitionsBaseAdapter.v) | `ImportedAbstractDefinitions` → `ImportedIbfSupply` |
| `ServiceBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedIbfSupply` |
| `ServiceNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedIbfSupply`; certificate module names in `Require` lines renamed; module named `ServiceNatBoolOperations` |
| `AbstractDefinitionsArrivalOperations` | [`certificates/AbstractDefinitionsArrivalOperations.v`](../../../../../../shared/certificates/AbstractDefinitionsArrivalOperations.v) | `ImportedAbstractDefinitions` → `ImportedIbfSupply` |
| `AbstractDefinitionsClasses` | [`certificates/AbstractDefinitionsClasses.v`](../../../../../../shared/certificates/AbstractDefinitionsClasses.v) | `ImportedAbstractDefinitions` → `ImportedIbfSupply` |
| `AbstractDefinitionsNatBoolOperations` | [`certificates/AbstractDefinitionsNatBoolOperations.v`](../../../../../../shared/certificates/AbstractDefinitionsNatBoolOperations.v) | `ImportedAbstractDefinitions` → `ImportedIbfSupply` |
| `AbstractDefinitionsIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedIbfSupply`; certificate module names in `Require` lines renamed; module named `AbstractDefinitionsIntervalOperations` |
| `AbstractDefinitionsOperations` | [`certificates/AbstractDefinitionsOperations.v`](../../../../../../shared/certificates/AbstractDefinitionsOperations.v) | `ImportedAbstractDefinitions` → `ImportedIbfSupply` |
| `AbstractDefinitionsSums` | [`certificates/AbstractDefinitionsSums.v`](../../../../../../shared/certificates/AbstractDefinitionsSums.v) | `ImportedAbstractDefinitions` → `ImportedIbfSupply` |
| `AbstractDefinitionsLogical` | [`certificates/AbstractDefinitionsLogical.v`](../../../../../../shared/certificates/AbstractDefinitionsLogical.v) | `ImportedAbstractDefinitions` → `ImportedIbfSupply` |
| `ServiceIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedIbfSupply` |
| `ServiceScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedIbfSupply` |
| `AbstractDefinitionsPendingOperations` | [`certificates/AbstractDefinitionsPendingOperations.v`](../../../../../../shared/certificates/AbstractDefinitionsPendingOperations.v) | `ImportedAbstractDefinitions` → `ImportedIbfSupply` |
| `AbstractDefinitionsTaskOperations` | [`certificates/AbstractDefinitionsTaskOperations.v`](../../../../../../shared/certificates/AbstractDefinitionsTaskOperations.v) | `ImportedAbstractDefinitions` → `ImportedIbfSupply` |
| `AbstractDefinitionsBusyIntervalHelpers` | [`certificates/AbstractDefinitionsBusyIntervalHelpers.v`](../../../../../../shared/certificates/AbstractDefinitionsBusyIntervalHelpers.v) | `ImportedBusyPrefix` → `ImportedIbfSupply` |
| `AbstractRtaHelpers` | [`certificates/AbstractRtaHelpers.v`](../../../../../../shared/certificates/AbstractRtaHelpers.v) | none |
| `SupplyScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedIbfSupply`; module named `SupplyScheduleBaseAdapter` |
| `SupplyScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedIbfSupply`; certificate module names in `Require` lines renamed; module named `SupplyScheduleFiniteOperations` |
| `SupplyScheduleOperations` | [`certificates/SupplyScheduleOperations.v`](../../../../../../shared/certificates/SupplyScheduleOperations.v) | `ImportedSupply` → `ImportedIbfSupply` |
| `SupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedIbfSupply`; module named `SupplyBaseAdapter` |
| `SupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../../shared/certificates/SupplyNatBoolOperations.v) | `ImportedSupply` → `ImportedIbfSupply` |
| `SupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedIbfSupply`; certificate module names in `Require` lines renamed; module named `SupplyIntervalOperations` |
| `SupplyCorrespondence` | [`certificates/SupplyCorrespondence.v`](../../../../../../shared/certificates/SupplyCorrespondence.v) | `ImportedSupply` → `ImportedIbfSupply` |
| `IbfSupplyCorrespondence` | [`certificates/IbfSupplyCorrespondence.v`](../../../../../../shared/certificates/IbfSupplyCorrespondence.v) | none |

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
| `SupplyComputationInterface` | [`lean_interfaces/SupplyComputationInterface.lean`](../../../../../../shared/lean_interfaces/SupplyComputationInterface.lean) |
| `AbstractRtaComputationInterface` | [`lean_interfaces/AbstractRtaComputationInterface.lean`](../../../../../../shared/lean_interfaces/AbstractRtaComputationInterface.lean) |
