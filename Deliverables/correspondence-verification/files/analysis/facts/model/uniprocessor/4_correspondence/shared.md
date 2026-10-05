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
| `UniPlatformScheduleBaseAdapter` | [`certificates/ScheduleBaseAdapter.v`](../../../../../../shared/certificates/ScheduleBaseAdapter.v) | `ImportedSchedule` → `ImportedUniprocessor`; module named `UniPlatformScheduleBaseAdapter` |
| `UniPlatformScheduleFiniteOperations` | [`certificates/ScheduleFiniteOperations.v`](../../../../../../shared/certificates/ScheduleFiniteOperations.v) | `ImportedSchedule` → `ImportedUniprocessor`; certificate module names in `Require` lines renamed; module named `UniPlatformScheduleFiniteOperations` |
| `UniPlatformScheduleCorrespondence` | [`certificates/ScheduleCorrespondence.v`](../../../../../../shared/certificates/ScheduleCorrespondence.v) | `ImportedSchedule` → `ImportedUniprocessor`; certificate module names in `Require` lines renamed; module named `UniPlatformScheduleCorrespondence` |
| `UniPlatformProcessorStateCorrespondence` | [`certificates/ScheduleProcessorStateCorrespondence.v`](../../../../../../shared/certificates/ScheduleProcessorStateCorrespondence.v) | `ImportedSchedule` → `ImportedUniprocessor`; certificate module names in `Require` lines renamed; module named `UniPlatformProcessorStateCorrespondence` |
