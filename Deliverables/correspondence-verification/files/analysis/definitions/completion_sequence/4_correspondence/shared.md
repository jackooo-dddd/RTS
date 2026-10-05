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
| `ArrivalSequenceBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedCompletionSequenceCombined` |
| `ServiceBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedCompletionSequenceCombined` |
| `ArrivalSequenceOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedCompletionSequenceCombined` |
| `ServiceNatBoolOperations` | [`certificates/ServiceNatBoolOperations.v`](../../../../../shared/certificates/ServiceNatBoolOperations.v) | `ImportedService` → `ImportedCompletionSequenceCombined` |
| `ArrivalSequenceCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedCompletionSequenceCombined` |
| `ServiceIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedCompletionSequenceCombined` |
| `ServiceJobOperations` | [`certificates/ServiceJobOperations.v`](../../../../../shared/certificates/ServiceJobOperations.v) | `ImportedService` → `ImportedCompletionSequenceCombined` |
| `ServiceScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedCompletionSequenceCombined` |
| `ServiceCorrespondence` | [`certificates/ServiceCorrespondence.v`](../../../../../shared/certificates/ServiceCorrespondence.v) | `ImportedService` → `ImportedCompletionSequenceCombined` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
