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
| `NonpreemptiveBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedNonpreemptive`; module named `NonpreemptiveBaseAdapter` |
| `NonpreemptiveNatBoolOperations` | [`certificates/ServiceNatBoolOperations.v`](../../../../../shared/certificates/ServiceNatBoolOperations.v) | `ImportedService` → `ImportedNonpreemptive`; certificate module names in `Require` lines renamed; module named `NonpreemptiveNatBoolOperations` |
| `NonpreemptiveIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedNonpreemptive`; certificate module names in `Require` lines renamed; module named `NonpreemptiveIntervalOperations` |
| `NonpreemptiveJobOperations` | [`certificates/ServiceJobOperations.v`](../../../../../shared/certificates/ServiceJobOperations.v) | `ImportedService` → `ImportedNonpreemptive`; certificate module names in `Require` lines renamed; module named `NonpreemptiveJobOperations` |
| `NonpreemptiveScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedNonpreemptive`; certificate module names in `Require` lines renamed; module named `NonpreemptiveScheduleOperations` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
