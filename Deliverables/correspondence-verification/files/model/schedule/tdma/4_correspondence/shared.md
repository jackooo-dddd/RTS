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
| `TdmaBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedTdmaProjectedFull`; module named `TdmaBaseAdapter` |
| `TdmaSeqsetAdapter` | [`certificates/SeqsetCorrespondence.v`](../../../../../shared/certificates/SeqsetCorrespondence.v) | `ImportedSeqset` → `ImportedTdmaProjectedFull`; module named `TdmaSeqsetAdapter` |
| `TdmaArithmeticAdapter` | [`certificates/TdmaArithmeticAdapter.v`](../../../../../shared/certificates/TdmaArithmeticAdapter.v) | none |
| `TdmaPolicyAdapter` | [`certificates/TdmaPolicyAdapter.v`](../../../../../shared/certificates/TdmaPolicyAdapter.v) | none |
| `TdmaValidityCorrespondence` | [`certificates/TdmaValidityCorrespondence.v`](../../../../../shared/certificates/TdmaValidityCorrespondence.v) | none |
| `TdmaNumericCorrespondence` | [`certificates/TdmaNumericCorrespondence.v`](../../../../../shared/certificates/TdmaNumericCorrespondence.v) | none |
