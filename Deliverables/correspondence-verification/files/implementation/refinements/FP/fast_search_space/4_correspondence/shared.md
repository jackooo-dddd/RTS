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
| `RfpBase` | [`certificates/RfpBase.v`](../../../../../../shared/certificates/RfpBase.v) | none |
| `RfpArrivalBound` | [`certificates/RacpArrivalBound.v`](../../../../../../shared/certificates/RacpArrivalBound.v) | `ImportedRefArrivalCurvePrefix` → `ImportedRefFPFastSearchSpace`; certificate module names in `Require` lines renamed; module named `RfpArrivalBound` |
| `RfpTask` | [`certificates/RacpTask.v`](../../../../../../shared/certificates/RacpTask.v) | `ImportedRefArrivalCurvePrefix` → `ImportedRefFPFastSearchSpace`; certificate module names in `Require` lines renamed; module named `RfpTask` |
| `RfpArrivalCurve` | [`certificates/RacpArrivalCurve.v`](../../../../../../shared/certificates/RacpArrivalCurve.v) | `ImportedRefArrivalCurvePrefix` → `ImportedRefFPFastSearchSpace`; certificate module names in `Require` lines renamed; module named `RfpArrivalCurve` |
| `RfpArrivalCurvePrefix` | [`certificates/RfsArrivalCurvePrefix.v`](../../../../../../shared/certificates/RfsArrivalCurvePrefix.v) | `ImportedRefFastSearchSpaceComputation` → `ImportedRefFPFastSearchSpace`; certificate module names in `Require` lines renamed; module named `RfpArrivalCurvePrefix` |
| `RfpFastSearchSpaceComputation` | [`certificates/RfpFastSearchSpaceComputation.v`](../../../../../../shared/certificates/RfpFastSearchSpaceComputation.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `DivModComputationInterface` | [`lean_interfaces/DivModComputationInterface.lean`](../../../../../../shared/lean_interfaces/DivModComputationInterface.lean) |
