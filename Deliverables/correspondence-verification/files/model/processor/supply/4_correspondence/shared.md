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
| `SupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedSupply`; module named `SupplyBaseAdapter` |
| `SupplyScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedSupply`; module named `SupplyScheduleBaseAdapter` |
| `SupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../shared/certificates/SupplyNatBoolOperations.v) | none |
| `SupplyScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedSupply`; certificate module names in `Require` lines renamed; module named `SupplyScheduleFiniteOperations` |
| `SupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedSupply`; certificate module names in `Require` lines renamed; module named `SupplyIntervalOperations` |
| `SupplyScheduleOperations` | [`certificates/SupplyScheduleOperations.v`](../../../../../shared/certificates/SupplyScheduleOperations.v) | none |
| `SupplyCorrespondence` | [`certificates/SupplyCorrespondence.v`](../../../../../shared/certificates/SupplyCorrespondence.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
