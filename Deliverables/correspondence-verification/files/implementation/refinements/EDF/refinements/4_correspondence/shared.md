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
| `RqArrivalBound` | [`certificates/RacArrivalBound.v`](../../../../../../shared/certificates/RacArrivalBound.v) | `ImportedRefArrivalCurve` → `ImportedRefEDFRefinements`; certificate module names in `Require` lines renamed; module named `RqArrivalBound` |
| `RqTask` | [`certificates/RacTask.v`](../../../../../../shared/certificates/RacTask.v) | `ImportedRefArrivalCurve` → `ImportedRefEDFRefinements`; certificate module names in `Require` lines renamed; module named `RqTask` |
| `RqArrivalCurve` | [`certificates/RrArrivalCurve.v`](../../../../../../shared/certificates/RrArrivalCurve.v) | `ImportedRefFPRefinements` → `ImportedRefEDFRefinements`; certificate module names in `Require` lines renamed; module named `RqArrivalCurve` |
| `RqArrivalCurvePrefix` | [`certificates/RfsArrivalCurvePrefix.v`](../../../../../../shared/certificates/RfsArrivalCurvePrefix.v) | `ImportedRefFastSearchSpaceComputation` → `ImportedRefEDFRefinements`; certificate module names in `Require` lines renamed; module named `RqArrivalCurvePrefix` |
| `RqFastSearchSpaceComputation` | [`certificates/RfpFastSearchSpaceComputation.v`](../../../../../../shared/certificates/RfpFastSearchSpaceComputation.v) | `ImportedRefFPFastSearchSpace` → `ImportedRefEDFRefinements`; certificate module names in `Require` lines renamed; module named `RqFastSearchSpaceComputation` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `DivModComputationInterface` | [`lean_interfaces/DivModComputationInterface.lean`](../../../../../../shared/lean_interfaces/DivModComputationInterface.lean) |
