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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedSporadicAsCurve`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedSporadicAsCurve`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedSporadicAsCurve`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedSporadicAsCurve` |
| `NatSubCorrespondence` | [`certificates/NatSubCorrespondence.v`](../../../../../../shared/certificates/NatSubCorrespondence.v) | `ImportedNat` → `ImportedSporadicAsCurve` |
| `DivModCorrespondence` | [`certificates/DivModCorrespondence.v`](../../../../../../shared/certificates/DivModCorrespondence.v) | `ImportedDivMod ImportedNat` → `ImportedSporadicAsCurve` |
| `CurvesCorrespondence` | [`certificates/CurvesCorrespondence.v`](../../../../../../shared/certificates/CurvesCorrespondence.v) | `ImportedCurves` → `ImportedSporadicAsCurve` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `DivModComputationInterface` | [`lean_interfaces/DivModComputationInterface.lean`](../../../../../../shared/lean_interfaces/DivModComputationInterface.lean) |
| `FactsSporadicArrivalBoundComputationInterface` | [`lean_interfaces/FactsSporadicArrivalBoundComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsSporadicArrivalBoundComputationInterface.lean) |
| `FactsArrivalCurvesComputationInterface` | [`lean_interfaces/FactsArrivalCurvesComputationInterface.lean`](../../../../../../shared/lean_interfaces/FactsArrivalCurvesComputationInterface.lean) |
