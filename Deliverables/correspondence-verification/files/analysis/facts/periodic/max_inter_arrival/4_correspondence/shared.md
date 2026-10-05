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
| `ArrivalsSeqBaseAdapter` | [`certificates/ArrivalSequenceBaseAdapter.v`](../../../../../../shared/certificates/ArrivalSequenceBaseAdapter.v) | `ImportedArrivalSequence` → `ImportedFactsPeriodicMaxInterArrival`; module named `ArrivalsSeqBaseAdapter` |
| `ArrivalsSeqOperations` | [`certificates/ArrivalSequenceOperations.v`](../../../../../../shared/certificates/ArrivalSequenceOperations.v) | `ImportedArrivalSequence` → `ImportedFactsPeriodicMaxInterArrival`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqOperations` |
| `ArrivalsSeqCorrespondence` | [`certificates/ArrivalSequenceCorrespondence.v`](../../../../../../shared/certificates/ArrivalSequenceCorrespondence.v) | `ImportedArrivalSequence` → `ImportedFactsPeriodicMaxInterArrival`; certificate module names in `Require` lines renamed; module named `ArrivalsSeqCorrespondence` |
| `ArrivalsCorrespondence` | [`certificates/ArrivalsCorrespondence.v`](../../../../../../shared/certificates/ArrivalsCorrespondence.v) | `ImportedArrivals` → `ImportedFactsPeriodicMaxInterArrival` |
| `PeriodicCorrespondence` | [`certificates/PeriodicCorrespondence-2.v`](../../../../../../shared/certificates/PeriodicCorrespondence-2.v) | `ImportedPeriodic` → `ImportedFactsPeriodicMaxInterArrival` |
| `TmiaCorrespondence` | [`certificates/TmiaCorrespondence.v`](../../../../../../shared/certificates/TmiaCorrespondence.v) | `ImportedTmia` → `ImportedFactsPeriodicMaxInterArrival` |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ArrivalsComputationInterface` | [`lean_interfaces/ArrivalsComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalsComputationInterface.lean) |
| `PeriodicComputationInterface` | [`lean_interfaces/PeriodicComputationInterface.lean`](../../../../../../shared/lean_interfaces/PeriodicComputationInterface.lean) |
| `PeriodicAsSporadicComputationInterface` | [`lean_interfaces/PeriodicAsSporadicComputationInterface.lean`](../../../../../../shared/lean_interfaces/PeriodicAsSporadicComputationInterface.lean) |
| `TmiaComputationInterface` | [`lean_interfaces/TmiaComputationInterface.lean`](../../../../../../shared/lean_interfaces/TmiaComputationInterface.lean) |
