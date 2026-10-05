# Shared modules used by this file

See [`shared/README.md`](../../../../../../shared/README.md).

## Common certificates

| Module | Shared file |
|---|---|
| `DivModCorrespondence` | [`certificates/common/DivModCorrespondence.v`](../../../../../../shared/certificates/common/DivModCorrespondence.v) |
| `LogicalRelation` | [`certificates/common/LogicalRelation.v`](../../../../../../shared/certificates/common/LogicalRelation.v) |
| `NatSubCorrespondence` | [`certificates/common/NatSubCorrespondence.v`](../../../../../../shared/certificates/common/NatSubCorrespondence.v) |
| `PropSPropFoundation` | [`certificates/common/PropSPropFoundation.v`](../../../../../../shared/certificates/common/PropSPropFoundation.v) |
| `SubadditivityNatCorrespondence` | [`certificates/common/SubadditivityNatCorrespondence.v`](../../../../../../shared/certificates/common/SubadditivityNatCorrespondence.v) |

## Shared certificates

| Module | Shared file | Differences in this file |
|---|---|---|
| `SupplyBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedPeriodic`; module named `SupplyBaseAdapter` |
| `SupplyScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedPeriodic`; module named `SupplyScheduleBaseAdapter` |
| `SupplyNatBoolOperations` | [`certificates/SupplyNatBoolOperations.v`](../../../../../../shared/certificates/SupplyNatBoolOperations.v) | `ImportedSupply` → `ImportedPeriodic` |
| `SupplyScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedPeriodic`; certificate module names in `Require` lines renamed; module named `SupplyScheduleFiniteOperations` |
| `SupplyIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedPeriodic`; certificate module names in `Require` lines renamed; module named `SupplyIntervalOperations` |
| `SupplyScheduleOperations` | [`certificates/SupplyScheduleOperations.v`](../../../../../../shared/certificates/SupplyScheduleOperations.v) | `ImportedSupply` → `ImportedPeriodic` |
| `SupplyCorrespondence` | [`certificates/SupplyCorrespondence.v`](../../../../../../shared/certificates/SupplyCorrespondence.v) | `ImportedSupply` → `ImportedPeriodic` |
| `PeriodicCorrespondence` | [`certificates/PeriodicCorrespondence.v`](../../../../../../shared/certificates/PeriodicCorrespondence.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
