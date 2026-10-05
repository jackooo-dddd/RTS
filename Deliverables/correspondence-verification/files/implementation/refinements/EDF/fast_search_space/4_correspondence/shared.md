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
| `ReBase` | [`certificates/RfpBase.v`](../../../../../../shared/certificates/RfpBase.v) | `ImportedRefFPFastSearchSpace` → `ImportedRefEDFFastSearchSpace`; module named `ReBase` |
| `ReArrivalBound` | [`certificates/RacpArrivalBound.v`](../../../../../../shared/certificates/RacpArrivalBound.v) | `ImportedRefArrivalCurvePrefix` → `ImportedRefEDFFastSearchSpace`; certificate module names in `Require` lines renamed; module named `ReArrivalBound` |
| `ReTask` | [`certificates/RacpTask.v`](../../../../../../shared/certificates/RacpTask.v) | `ImportedRefArrivalCurvePrefix` → `ImportedRefEDFFastSearchSpace`; certificate module names in `Require` lines renamed; module named `ReTask` |
| `ReArrivalCurve` | [`certificates/RacpArrivalCurve.v`](../../../../../../shared/certificates/RacpArrivalCurve.v) | `ImportedRefArrivalCurvePrefix` → `ImportedRefEDFFastSearchSpace`; certificate module names in `Require` lines renamed; module named `ReArrivalCurve` |
| `ReFastSearchSpaceComputation` | [`certificates/RfpFastSearchSpaceComputation.v`](../../../../../../shared/certificates/RfpFastSearchSpaceComputation.v) | `ImportedRefFPFastSearchSpace` → `ImportedRefEDFFastSearchSpace`; certificate module names in `Require` lines renamed; module named `ReFastSearchSpaceComputation` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `DivModComputationInterface` | [`lean_interfaces/DivModComputationInterface.lean`](../../../../../../shared/lean_interfaces/DivModComputationInterface.lean) |
