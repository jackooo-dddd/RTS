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
| `FtdmaBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedFactsTdma`; module named `FtdmaBaseAdapter` |
| `FtdmaSeqsetAdapter` | [`certificates/SeqsetCorrespondence.v`](../../../../../shared/certificates/SeqsetCorrespondence.v) | `ImportedSeqset` → `ImportedFactsTdma`; module named `FtdmaSeqsetAdapter` |
| `FtdmaArithmeticAdapter` | [`certificates/TdmaArithmeticAdapter.v`](../../../../../shared/certificates/TdmaArithmeticAdapter.v) | `ImportedTdmaProjectedFull` → `ImportedFactsTdma`; certificate module names in `Require` lines renamed; module named `FtdmaArithmeticAdapter` |
| `FtdmaPolicyAdapter` | [`certificates/TdmaPolicyAdapter.v`](../../../../../shared/certificates/TdmaPolicyAdapter.v) | `ImportedTdmaProjectedFull` → `ImportedFactsTdma`; certificate module names in `Require` lines renamed; module named `FtdmaPolicyAdapter` |
| `FtdmaValidityCorrespondence` | [`certificates/TdmaValidityCorrespondence.v`](../../../../../shared/certificates/TdmaValidityCorrespondence.v) | `ImportedTdmaProjectedFull` → `ImportedFactsTdma`; certificate module names in `Require` lines renamed; module named `FtdmaValidityCorrespondence` |
| `FtdmaNumericCorrespondence` | [`certificates/TdmaNumericCorrespondence.v`](../../../../../shared/certificates/TdmaNumericCorrespondence.v) | `ImportedTdmaProjectedFull` → `ImportedFactsTdma`; certificate module names in `Require` lines renamed; module named `FtdmaNumericCorrespondence` |
