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
| `RrArrivalBound` | [`certificates/RacArrivalBound.v`](../../../../../../shared/certificates/RacArrivalBound.v) | `ImportedRefArrivalCurve` → `ImportedRefFPRefinements`; certificate module names in `Require` lines renamed; module named `RrArrivalBound` |
| `RrTask` | [`certificates/RacTask.v`](../../../../../../shared/certificates/RacTask.v) | `ImportedRefArrivalCurve` → `ImportedRefFPRefinements`; certificate module names in `Require` lines renamed; module named `RrTask` |
| `RrArrivalCurve` | [`certificates/RrArrivalCurve.v`](../../../../../../shared/certificates/RrArrivalCurve.v) | none |
| `RrArrivalCurvePrefix` | [`certificates/RfsArrivalCurvePrefix.v`](../../../../../../shared/certificates/RfsArrivalCurvePrefix.v) | `ImportedRefFastSearchSpaceComputation` → `ImportedRefFPRefinements`; certificate module names in `Require` lines renamed; module named `RrArrivalCurvePrefix` |
| `RrFastSearchSpaceComputation` | [`certificates/RfpFastSearchSpaceComputation.v`](../../../../../../shared/certificates/RfpFastSearchSpaceComputation.v) | `ImportedRefFPFastSearchSpace` → `ImportedRefFPRefinements`; certificate module names in `Require` lines renamed; module named `RrFastSearchSpaceComputation` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `DivModComputationInterface` | [`lean_interfaces/DivModComputationInterface.lean`](../../../../../../shared/lean_interfaces/DivModComputationInterface.lean) |
