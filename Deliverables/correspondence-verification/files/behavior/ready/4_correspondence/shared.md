# Shared modules used by this file

See [`shared/README.md`](../../../../shared/README.md).

## Common certificates

| Module | Shared file |
|---|---|
| `LogicalRelation` | [`certificates/common/LogicalRelation.v`](../../../../shared/certificates/common/LogicalRelation.v) |
| `PropSPropFoundation` | [`certificates/common/PropSPropFoundation.v`](../../../../shared/certificates/common/PropSPropFoundation.v) |
| `SubadditivityNatCorrespondence` | [`certificates/common/SubadditivityNatCorrespondence.v`](../../../../shared/certificates/common/SubadditivityNatCorrespondence.v) |

## Shared certificates

| Module | Shared file | Differences in this file |
|---|---|---|
| `ReadyArrivalBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedReady`; module named `ReadyArrivalBaseAdapter` |
| `ReadyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedReady`; module named `ReadyBaseAdapter` |
| `ReadyArrivalOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedReady`; certificate module names in `Require` lines renamed; module named `ReadyArrivalOperations` |
| `ReadyNatBoolOperations` | [`certificates/ServiceNatBoolOperations.v`](../../../../shared/certificates/ServiceNatBoolOperations.v) | `ImportedService` → `ImportedReady`; certificate module names in `Require` lines renamed; module named `ReadyNatBoolOperations` |
| `ReadyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedReady`; certificate module names in `Require` lines renamed; module named `ReadyIntervalOperations` |
| `ReadyJobOperations` | [`certificates/ServiceJobOperations.v`](../../../../shared/certificates/ServiceJobOperations.v) | `ImportedService` → `ImportedReady`; certificate module names in `Require` lines renamed; module named `ReadyJobOperations` |
| `ReadyScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedReady`; certificate module names in `Require` lines renamed; module named `ReadyScheduleOperations` |
| `ReadyServiceCorrespondence` | [`certificates/ReadyServiceCorrespondence.v`](../../../../shared/certificates/ReadyServiceCorrespondence.v) | none |
| `ReadyCorrespondence` | [`certificates/ReadyCorrespondence.v`](../../../../shared/certificates/ReadyCorrespondence.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
