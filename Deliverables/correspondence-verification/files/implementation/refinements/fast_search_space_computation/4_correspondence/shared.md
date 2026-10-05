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
| `RfsArrivalBound` | [`certificates/RacpArrivalBound.v`](../../../../../shared/certificates/RacpArrivalBound.v) | `ImportedRefArrivalCurvePrefix` → `ImportedRefFastSearchSpaceComputation`; certificate module names in `Require` lines renamed; module named `RfsArrivalBound` |
| `RfsTask` | [`certificates/RacpTask.v`](../../../../../shared/certificates/RacpTask.v) | `ImportedRefArrivalCurvePrefix` → `ImportedRefFastSearchSpaceComputation`; certificate module names in `Require` lines renamed; module named `RfsTask` |
| `RfsArrivalCurve` | [`certificates/RacpArrivalCurve.v`](../../../../../shared/certificates/RacpArrivalCurve.v) | `ImportedRefArrivalCurvePrefix` → `ImportedRefFastSearchSpaceComputation`; certificate module names in `Require` lines renamed; module named `RfsArrivalCurve` |
| `RfsArrivalCurvePrefix` | [`certificates/RfsArrivalCurvePrefix.v`](../../../../../shared/certificates/RfsArrivalCurvePrefix.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `DivModComputationInterface` | [`lean_interfaces/DivModComputationInterface.lean`](../../../../../shared/lean_interfaces/DivModComputationInterface.lean) |
