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
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence.v`](../../../../../shared/certificates/NatSubCorrespondence.v) | `ImportedNat` → `ImportedPriorityGel` |
| `PcoBaseAdapter` | [`certificates/PriorityBaseAdapter.v`](../../../../../shared/certificates/PriorityBaseAdapter.v) | `ImportedPriorityDefinitions` → `ImportedPriorityGel`; module named `PcoBaseAdapter` |
| `PcoStaticOrder` | [`certificates/PcoStaticOrder.v`](../../../../../shared/certificates/PcoStaticOrder.v) | `ImportedPriorityCoercion` → `ImportedPriorityGel` |
| `PcoDynamicOrder` | [`certificates/PcoDynamicOrder.v`](../../../../../shared/certificates/PcoDynamicOrder.v) | `ImportedPriorityCoercion` → `ImportedPriorityGel` |
| `PriorityCoercionCorrespondence` | [`certificates/PriorityCoercionCorrespondence.v`](../../../../../shared/certificates/PriorityCoercionCorrespondence.v) | `ImportedPriorityCoercion` → `ImportedPriorityGel` |
| `PriorityGelCorrespondence` | [`certificates/PriorityGelCorrespondence.v`](../../../../../shared/certificates/PriorityGelCorrespondence.v) | none |
