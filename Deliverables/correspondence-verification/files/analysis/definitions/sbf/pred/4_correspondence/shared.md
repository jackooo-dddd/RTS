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
| `ArrivalSequenceBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedPred` |
| `SupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedPred`; module named `SupplyBaseAdapter` |
| `SupplyScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedPred`; module named `SupplyScheduleBaseAdapter` |
| `ArrivalSequenceOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedPred` |
| `SupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../../shared/certificates/SupplyNatBoolOperations.v) | `ImportedSupply` → `ImportedPred` |
| `SupplyScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedPred`; certificate module names in `Require` lines renamed; module named `SupplyScheduleFiniteOperations` |
| `ArrivalSequenceCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedPred` |
| `SupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedPred`; certificate module names in `Require` lines renamed; module named `SupplyIntervalOperations` |
| `SupplyScheduleOperations` | [`certificates/SupplyScheduleOperations.v`](../../../../../../shared/certificates/SupplyScheduleOperations.v) | `ImportedSupply` → `ImportedPred` |
| `SupplyCorrespondence` | [`certificates/SupplyCorrespondence.v`](../../../../../../shared/certificates/SupplyCorrespondence.v) | `ImportedSupply` → `ImportedPred` |
| `PredCorrespondence` | [`certificates/PredCorrespondence.v`](../../../../../../shared/certificates/PredCorrespondence.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
