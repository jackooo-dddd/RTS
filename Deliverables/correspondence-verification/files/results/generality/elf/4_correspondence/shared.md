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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedGeneralityElf`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedGeneralityElf`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedGeneralityElf`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `JitterSvcBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedGeneralityElf`; module named `JitterSvcBaseAdapter` |
| `JitterSvcNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedGeneralityElf`; certificate module names in `Require` lines renamed; module named `JitterSvcNatBoolOperations` |
| `JitterSvcIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedGeneralityElf`; certificate module names in `Require` lines renamed; module named `JitterSvcIntervalOperations` |
| `JitterSvcScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedGeneralityElf`; certificate module names in `Require` lines renamed; module named `JitterSvcScheduleOperations` |
| `JitterSvcJobOperations` | [`certificates/BasicJobOperations.v`](../../../../../shared/certificates/BasicJobOperations.v) | `ImportedReadinessBasicProjection` → `ImportedGeneralityElf`; certificate module names in `Require` lines renamed; module named `JitterSvcJobOperations` |
| `PreemptionParameterCorrespondence` | [`certificates/PreemptionParameterCorrespondence.v`](../../../../../shared/certificates/PreemptionParameterCorrespondence.v) | `ImportedPreemptionParameter` → `ImportedGeneralityElf` |
| `PreemptionTimeCorrespondence` | [`certificates/PreemptionTimeCorrespondence.v`](../../../../../shared/certificates/PreemptionTimeCorrespondence.v) | `ImportedPreemptionTime` → `ImportedGeneralityElf` |
| `PriorityDrivenCorrespondence` | [`certificates/PriorityDrivenCorrespondence.v`](../../../../../shared/certificates/PriorityDrivenCorrespondence.v) | `ImportedPriorityDriven` → `ImportedGeneralityElf` |
| `PStateCoverHelpers` | [`certificates/PStateCoverHelpers.v`](../../../../../shared/certificates/PStateCoverHelpers.v) | `ImportedFactsJitter` → `ImportedGeneralityElf` |
| `FactsPreemptionHelpers` | [`certificates/FactsPreemptionHelpers.v`](../../../../../shared/certificates/FactsPreemptionHelpers.v) | `ImportedFactsJitter` → `ImportedGeneralityElf` |
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence.v`](../../../../../shared/certificates/NatSubCorrespondence.v) | `ImportedNat` → `ImportedGeneralityElf` |
| `PcoBaseAdapter` | [`certificates/PriorityBaseAdapter.v`](../../../../../shared/certificates/PriorityBaseAdapter.v) | `ImportedPriorityDefinitions` → `ImportedGeneralityElf`; module named `PcoBaseAdapter` |
| `PcoStaticOrder` | [`certificates/PcoStaticOrder.v`](../../../../../shared/certificates/PcoStaticOrder.v) | `ImportedPriorityCoercion` → `ImportedGeneralityElf` |
| `PcoDynamicOrder` | [`certificates/PcoDynamicOrder.v`](../../../../../shared/certificates/PcoDynamicOrder.v) | `ImportedPriorityCoercion` → `ImportedGeneralityElf` |
| `PriorityCoercionCorrespondence` | [`certificates/PriorityCoercionCorrespondence.v`](../../../../../shared/certificates/PriorityCoercionCorrespondence.v) | `ImportedPriorityCoercion` → `ImportedGeneralityElf` |
| `PriorityGelHelpers` | [`certificates/PriorityGelHelpers.v`](../../../../../shared/certificates/PriorityGelHelpers.v) | `ImportedBlockingBoundElf` → `ImportedGeneralityElf` |
| `PriorityElfHelpers` | [`certificates/PriorityElfCorrespondence.v`](../../../../../shared/certificates/PriorityElfCorrespondence.v) | `ImportedPriorityElf` → `ImportedGeneralityElf`; certificate module names in `Require` lines renamed; module named `PriorityElfHelpers` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `PreemptionTimeComputationInterface` | [`lean_interfaces/PreemptionTimeComputationInterface.lean`](../../../../../shared/lean_interfaces/PreemptionTimeComputationInterface.lean) |
| `PriorityDrivenComputationInterface` | [`lean_interfaces/PriorityDrivenComputationInterface.lean`](../../../../../shared/lean_interfaces/PriorityDrivenComputationInterface.lean) |
| `ScheduledComputationInterface` | [`lean_interfaces/ScheduledComputationInterface.lean`](../../../../../shared/lean_interfaces/ScheduledComputationInterface.lean) |
| `ProcessorStateCoverInterface` | [`lean_interfaces/ProcessorStateCoverInterface.lean`](../../../../../shared/lean_interfaces/ProcessorStateCoverInterface.lean) |
| `FactsPreemptionComputationInterface` | [`lean_interfaces/FactsPreemptionComputationInterface.lean`](../../../../../shared/lean_interfaces/FactsPreemptionComputationInterface.lean) |
| `PriorityGelComputationInterface` | [`lean_interfaces/PriorityGelComputationInterface.lean`](../../../../../shared/lean_interfaces/PriorityGelComputationInterface.lean) |
| `FactsPriorityGelComputationInterface` | [`lean_interfaces/FactsPriorityGelComputationInterface.lean`](../../../../../shared/lean_interfaces/FactsPriorityGelComputationInterface.lean) |
| `PriorityElfComputationInterface` | [`lean_interfaces/PriorityElfComputationInterface.lean`](../../../../../shared/lean_interfaces/PriorityElfComputationInterface.lean) |
| `FactsPriorityElfComputationInterface` | [`lean_interfaces/FactsPriorityElfComputationInterface.lean`](../../../../../shared/lean_interfaces/FactsPriorityElfComputationInterface.lean) |
