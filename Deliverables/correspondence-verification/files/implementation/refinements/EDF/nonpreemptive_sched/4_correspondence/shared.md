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
| `PsEac` | [`certificates/EacFullCorrespondence.v`](../../../../../../shared/certificates/EacFullCorrespondence.v) | `ImportedJobConstructor` → `ImportedRefEDFNPSched`; module named `PsEac` |
| `PsAb` | [`certificates/AbCorrespondence.v`](../../../../../../shared/certificates/AbCorrespondence.v) | `ImportedJobConstructor` → `ImportedRefEDFNPSched`; certificate module names in `Require` lines renamed; module named `PsAb` |
| `PsImplTask` | [`certificates/ImplTaskCorrespondence.v`](../../../../../../shared/certificates/ImplTaskCorrespondence.v) | `ImportedJobConstructor` → `ImportedRefEDFNPSched`; certificate module names in `Require` lines renamed; module named `PsImplTask` |
| `PsListOps` | [`certificates/JcListOps.v`](../../../../../../shared/certificates/JcListOps.v) | `ImportedFactsJobConstructor` → `ImportedRefEDFNPSched`; module named `PsListOps` |
| `PsSvcBase` | [`certificates/ServiceBaseAdapter.v`](../../../../../../shared/certificates/ServiceBaseAdapter.v) | `ImportedService` → `ImportedRefEDFNPSched`; module named `PsSvcBase` |
| `PsSvcNatBool` | [`certificates/BasicNatBoolOperations.v`](../../../../../../shared/certificates/BasicNatBoolOperations.v) | `ImportedReadinessBasicProjection` → `ImportedRefEDFNPSched`; certificate module names in `Require` lines renamed; module named `PsSvcNatBool` |
| `PsSvcInterval` | [`certificates/ServiceIntervalOperations.v`](../../../../../../shared/certificates/ServiceIntervalOperations.v) | `ImportedService` → `ImportedRefEDFNPSched`; certificate module names in `Require` lines renamed; module named `PsSvcInterval` |
| `PsSched` | [`certificates/PsSched.v`](../../../../../../shared/certificates/PsSched.v) | none |

## Lean interfaces

| Interface | Shared file |
|---|---|
| `NondecreasingComputationInterface` | [`lean_interfaces/NondecreasingComputationInterface.lean`](../../../../../../shared/lean_interfaces/NondecreasingComputationInterface.lean) |
| `BigcatComputationInterface` | [`lean_interfaces/BigcatComputationInterface.lean`](../../../../../../shared/lean_interfaces/BigcatComputationInterface.lean) |
| `ArrivalSequenceComputationInterface` | [`lean_interfaces/ArrivalSequenceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ArrivalSequenceComputationInterface.lean) |
| `ScheduleComputationInterface` | [`lean_interfaces/ScheduleComputationInterface.lean`](../../../../../../shared/lean_interfaces/ScheduleComputationInterface.lean) |
| `ServiceComputationInterface` | [`lean_interfaces/ServiceComputationInterface.lean`](../../../../../../shared/lean_interfaces/ServiceComputationInterface.lean) |
| `PreemptionParameterComputationInterface` | [`lean_interfaces/PreemptionParameterComputationInterface.lean`](../../../../../../shared/lean_interfaces/PreemptionParameterComputationInterface.lean) |
| `TransformPrefixComputationInterface` | [`lean_interfaces/TransformPrefixComputationInterface.lean`](../../../../../../shared/lean_interfaces/TransformPrefixComputationInterface.lean) |
| `IdealUniSchedulerComputationInterface` | [`lean_interfaces/IdealUniSchedulerComputationInterface.lean`](../../../../../../shared/lean_interfaces/IdealUniSchedulerComputationInterface.lean) |
| `ExtrapolatedArrivalCurveArithmeticInterface` | [`lean_interfaces/ExtrapolatedArrivalCurveArithmeticInterface.lean`](../../../../../../shared/lean_interfaces/ExtrapolatedArrivalCurveArithmeticInterface.lean) |
| `RefSchedComputationInterface` | [`lean_interfaces/RefSchedComputationInterface.lean`](../../../../../../shared/lean_interfaces/RefSchedComputationInterface.lean) |
