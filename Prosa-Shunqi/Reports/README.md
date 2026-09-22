# Reports

## Canonical file reports

Each authoritative Prosa v0.6 source file has at most one current report at:

```text
Reports/files/<source-directory>/<first-report-timestamp>_<source-basename>.md
```

Once work starts on a source file, its translation batches, blockers,
revalidation runs, fixes, and final acceptance are appended to that file's
canonical report. The leading timestamp is copied from the earliest historical
report that covered the source file, uses no timezone suffix, and is not
changed on later updates. Do not create another report for the same source
file. File existence is not acceptance; the machine-readable status and
manifest files under `Validation/planning/v06_pipeline/` remain authoritative.

Current canonical reports, in the approved execution order:

| Rank | Source file | Canonical report | Current file status |
|---:|---|---|---|
| 1 | `behavior/time.v` | [time](files/behavior/2026-09-20_210930_time.md) | `ACCEPTED_V06_FILE` |
| 2 | `util/tactics.v` | [tactics](files/util/2026-09-20_214230_tactics.md) | `ACCEPTED_V06_FILE` |
| 3 | `util/notation.v` | [notation](files/util/2026-09-20_214230_notation.md) | `ACCEPTED_V06_FILE` |
| 4 | `util/rel.v` | [rel](files/util/2026-09-20_214230_rel.md) | `ACCEPTED_V06_FILE` |
| 5 | `util/seqset.v` | [seqset](files/util/2026-09-20_214230_seqset.md) | `ACCEPTED_V06_FILE` |
| 6 | `util/subadditivity.v` | [subadditivity](files/util/2026-09-20_214230_subadditivity.md) | `ACCEPTED_V06_FILE` |
| 7 | `util/supremum.v` | [supremum](files/util/2026-09-20_214230_supremum.md) | `ACCEPTED_V06_FILE` |
| 8 | `util/nat.v` | [nat](files/util/2026-09-21_082258_nat.md) | `ACCEPTED_V06_FILE` |
| 9 | `util/unit_growth.v` | [unit_growth](files/util/2026-09-21_082258_unit_growth.md) | `ACCEPTED_V06_FILE` |
| 10 | `util/search_arg.v` | [search_arg](files/util/2026-09-21_082258_search_arg.md) | `ACCEPTED_V06_FILE` |
| 11 | `util/list.v` | [list](files/util/2026-09-21_082258_list.md) | `ACCEPTED_V06_FILE` |
| 12 | `util/sum.v` | [sum](files/util/2026-09-21_082258_sum.md) | `ACCEPTED_V06_FILE` |
| 13 | `util/epsilon.v` | [epsilon](files/util/2026-09-22_034433_epsilon.md) | `ACCEPTED_V06_FILE` |
| 14 | `util/bigop.v` | [bigop](files/util/2026-09-22_034433_bigop.md) | `ACCEPTED_V06_FILE` |
| 15 | `util/setoid.v` | [setoid](files/util/2026-09-22_042247_setoid.md) | `ACCEPTED_V06_FILE` |
| 16 | `util/poet.v` | [poet](files/util/2026-09-22_044913_poet.md) | `ACCEPTED_V06_FILE` |
| 17 | `util/bigcat.v` | [bigcat](files/util/2026-09-22_053020_bigcat.md) | `TRANSLATION_IN_PROGRESS` |

The formal scheduling document is
[`../v06_file_translation_order.md`](../v06_file_translation_order.md).
Dependency readiness still comes from the accepted file DAG, not from report
text.

## Legacy and raw evidence

`Reports/legacy/` retains the former date-named, multi-file, and batch reports
with their original bytes. Canonical reports record each legacy filename and
hash. Intermediate PASS entries in a legacy report remain intermediate; only
the later publication gate can establish final acceptance.

Raw machine logs and intermediate evidence belong under `Validation/logs/`,
not here.

## Continuous-run summaries

Cross-file execution summaries requested for a specific run live under
`Reports/runs/`. They record chronological progress and final outcomes for
that run, but never override canonical per-file reports or machine-readable
pipeline status. Current run:

- [2026-09-22 translation-order continuous run](runs/2026-09-22_000308_translation_order_continuous_run.md)
