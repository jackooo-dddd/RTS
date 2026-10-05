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
| `AbstractDefinitionsBaseAdapter` | [`certificates/AbstractDefinitionsBaseAdapter.v`](../../../../../shared/certificates/AbstractDefinitionsBaseAdapter.v) | none |
| `ServiceBaseAdapter` | [`certificates/ServiceBaseAdapter.v`](../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedAbstractDefinitions` |
| `AbstractDefinitionsClasses` | [`certificates/AbstractDefinitionsClasses.v`](../../../../../shared/certificates/AbstractDefinitionsClasses.v) | none |
| `AbstractDefinitionsNatBoolOperations` | [`certificates/AbstractDefinitionsNatBoolOperations.v`](../../../../../shared/certificates/AbstractDefinitionsNatBoolOperations.v) | none |
| `ServiceNatBoolOperations` | [`certificates/BasicNatBoolOperations.v`](../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedAbstractDefinitions`; certificate module names in `Require` lines renamed; module named `ServiceNatBoolOperations` |
| `AbstractDefinitionsArrivalOperations` | [`certificates/AbstractDefinitionsArrivalOperations.v`](../../../../../shared/certificates/AbstractDefinitionsArrivalOperations.v) | none |
| `AbstractDefinitionsIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedAbstractDefinitions`; certificate module names in `Require` lines renamed; module named `AbstractDefinitionsIntervalOperations` |
| `AbstractDefinitionsOperations` | [`certificates/AbstractDefinitionsOperations.v`](../../../../../shared/certificates/AbstractDefinitionsOperations.v) | none |
| `AbstractDefinitionsTaskOperations` | [`certificates/AbstractDefinitionsTaskOperations.v`](../../../../../shared/certificates/AbstractDefinitionsTaskOperations.v) | none |
| `ServiceIntervalOperations` | [`certificates/ServiceIntervalOperations.v`](../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedAbstractDefinitions` |
| `AbstractDefinitionsSums` | [`certificates/AbstractDefinitionsSums.v`](../../../../../shared/certificates/AbstractDefinitionsSums.v) | none |
| `ServiceScheduleOperations` | [`certificates/ServiceScheduleOperations.v`](../../../../../shared/certificates/ServiceScheduleOperations.v) | `ImportedService` → `ImportedAbstractDefinitions` |
| `AbstractDefinitionsLogical` | [`certificates/AbstractDefinitionsLogical.v`](../../../../../shared/certificates/AbstractDefinitionsLogical.v) | none |
| `AbstractDefinitionsPendingOperations` | [`certificates/AbstractDefinitionsPendingOperations.v`](../../../../../shared/certificates/AbstractDefinitionsPendingOperations.v) | none |
| `AbstractDefinitionsBusyInterval` | [`certificates/AbstractDefinitionsBusyInterval.v`](../../../../../shared/certificates/AbstractDefinitionsBusyInterval.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
