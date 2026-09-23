# Reports

## Latest published validation

The latest formally published file is `analysis/definitions/sbf/plain.v` (42/357 files, 336/2439 declarations accepted):

- [canonical plain-SBF report](files/analysis/definitions/sbf/2026-09-24_062700_plain.md)
- [canonical analysis service report](files/analysis/definitions/2026-09-24_060952_service.md)
- [canonical predicate-SBF report](files/analysis/definitions/sbf/2026-09-24_053710_pred.md)
- [canonical periodic-resource report](files/analysis/definitions/sbf/2026-09-24_051850_periodic.md)
- [canonical average-resource report](files/analysis/definitions/sbf/2026-09-24_043858_average.md)
- [canonical finish-time report](files/analysis/definitions/2026-09-24_035607_finish_time.md)
- [canonical completion-sequence report](files/analysis/definitions/2026-09-24_031052_completion_sequence.md)
- [canonical extrapolated-arrival-curve facts report](files/implementation/facts/2026-09-24_014411_extrapolated_arrival_curve.md)
- [canonical arrival-bound report](files/implementation/definitions/2026-09-24_010800_arrival_bound.md)
- [canonical SBF report](files/analysis/definitions/sbf/2026-09-24_005022_sbf.md)
- [canonical extrapolated-arrival-curve report](files/implementation/definitions/2026-09-23_211129_extrapolated_arrival_curve.md)
- [canonical Superadditivity report](files/util/2026-09-23_160337_superadditivity.md)
- [canonical Fixpoint report](files/util/2026-09-23_150425_fixpoint.md)
- [latest Fixpoint closure run](runs/2026-09-23_1848_fixpoint_closure_run.md)
- [earlier continuous-run summary](runs/2026-09-22_000308_translation_order_continuous_run.md)
- machine authority:
  `../Validation/planning/v06_pipeline/analysis_sbf_plain_module_status.json`

The three plain-SBF declarations compose certified predicate-SBF and supply
relations. The theorem statement is checked with a separate official/imported
exact-type guard; the semantic certificate is proof-independent. The approved
Prop/SProp boundary remains visible; no semantic premise or unexpected
assumption is accepted.

The two `analysis/definitions/service.v` definitions have actual-artifact
Rocq correspondences composed from accepted Service/ArrivalSequence bridges,
ordered filtering, and a kernel-proved optional-head bridge. Both assumption
audits expose the approved Prop/SProp foundation with no semantic premise or
theorem self-dependency.

The five predicate-SBF declarations have actual-artifact Rocq correspondence,
including the full quantified theorem statement; the theorem proof constants
are absent from its semantic certificate. All five expose the approved
Prop/SProp foundation and no semantic premises. The two periodic-resource
definitions have actual-artifact Rocq correspondence,
including the full quantified supply bound and the truncated-Nat SBF formula;
both expose the approved Prop/SProp foundation and no semantic premises.
The two average-resource definitions have actual-artifact Rocq
correspondence, reusing accepted Supply and DivMod operation relations on
the same imported artifact. Their assumption audits expose only the approved
Prop/SProp foundation alongside importer primitives. The five `finish_time.v`
declarations have actual-artifact Rocq
correspondence. The reusable MathComp `ex_minn` ↔ imported Lean `Nat.find`
least-witness bridge is kernel-checked and the three theorem statements have
separate exact-type guards. Their assumption audit exposes the Prop/SProp
foundation and reports no semantic premise or theorem self-dependency.
The `completion_sequence` definition has an actual-artifact Rocq
correspondence composed from certified `arrivals_up_to`, `completes_at`, and
ordered `filter` relations, with the Prop/SProp foundation visible in the
assumption audit. All ten extrapolated-arrival-curve facts have actual-artifact theorem
statement correspondence with the explicit Prop/SProp foundation. Before
that, the official arrival-bound inductive, Boolean equality, and informative
reflection view passed actual-artifact semantic validation and publication.
The equality/view correspondence explicitly uses the Prop/SProp foundation;
the constructor relation does not. The SBF class was also accepted without
that foundation. Earlier, all 21
ExtrapolatedArrivalCurve declarations passed (5 `CERTIFIED`, 16 with the
explicit foundation). Current machine-published coverage is **40 / 357 files** and **331 / 2439
declarations**, with **0** translated but uncertified declarations in the
published coverage. Reports are organized below `files/` and `runs/`;
this README is the visible entry point rather than a duplicate status
authority.

## Latest work in progress

The earlier ordered candidate `util/lcmseq.v` (rank 30) remains unaccepted.
Its five Lean declarations are proof-clean, but imported arithmetic proof-field
statement-only dependencies still block whole-file publication. Rank 33
`implementation/definitions/extrapolated_arrival_curve.v` is now fully
published. The next unfinished file must be selected from the current machine
status and file DAG; this README does not assert its readiness.

Work-in-progress reports appear here even though they do not change the
formally published coverage above. Their presence never implies
`ACCEPTED_V06_FILE`; acceptance remains controlled by machine manifests.

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
| 17 | `util/bigcat.v` | [bigcat](files/util/2026-09-22_053020_bigcat.md) | `ACCEPTED_V06_FILE` |
| 18 | `util/minmax.v` | [minmax](files/util/2026-09-22_082537_minmax.md) | `ACCEPTED_V06_FILE` |
| 19 | `util/div_mod.v` | [div_mod](files/util/2026-09-22_103919_div_mod.md) | `ACCEPTED_V06_FILE` |
| 20 | `util/nondecreasing.v` | [nondecreasing](files/util/2026-09-22_133028_nondecreasing.md) | `ACCEPTED_V06_FILE` |
| 21 | `util/all.v` | [all](files/util/2026-09-22_203705_all.md) | `ACCEPTED_V06_FILE` |
| 22 | `behavior/job.v` | [job](files/behavior/2026-09-22_210645_job.md) | `ACCEPTED_V06_FILE` |
| 23 | `behavior/arrival_sequence.v` | [arrival_sequence](files/behavior/2026-09-22_222929_arrival_sequence.md) | `ACCEPTED_V06_FILE` |
| 24 | `behavior/schedule.v` | [schedule](files/behavior/2026-09-23_002720_schedule.md) | `ACCEPTED_V06_FILE` |
| 25 | `behavior/service.v` | [service](files/behavior/2026-09-23_023952_service.md) | `ACCEPTED_V06_FILE` |
| 26 | `behavior/ready.v` | [ready](files/behavior/2026-09-23_042533_ready.md) | `ACCEPTED_V06_FILE` |
| 27 | `behavior/all.v` | [all](files/behavior/2026-09-23_054506_all.md) | `ACCEPTED_V06_FILE` |
| 28 | `model/processor/supply.v` | [supply](files/model/processor/2026-09-23_055700_supply.md) | `ACCEPTED_V06_FILE` |
| 29 | `util/int.v` | [int](files/util/2026-09-23_072030_int.md) | `ACCEPTED_V06_FILE` |
| 30 | `util/lcmseq.v` | [lcmseq](files/util/2026-09-23_073256_lcmseq.md) | `NOT_ACCEPTED` |
| 31 | `util/fixpoint.v` | [fixpoint](files/util/2026-09-23_150425_fixpoint.md) | `ACCEPTED_V06_FILE` |
| 32 | `util/superadditivity.v` | [superadditivity](files/util/2026-09-23_160337_superadditivity.md) | `ACCEPTED_V06_FILE` |
| 33 | `implementation/definitions/extrapolated_arrival_curve.v` | [extrapolated_arrival_curve](files/implementation/definitions/2026-09-23_211129_extrapolated_arrival_curve.md) | `ACCEPTED_V06_FILE` |
| 34 | `analysis/definitions/sbf/sbf.v` | [sbf](files/analysis/definitions/sbf/2026-09-24_005022_sbf.md) | `ACCEPTED_V06_FILE` |
| 35 | `implementation/definitions/arrival_bound.v` | [arrival_bound](files/implementation/definitions/2026-09-24_010800_arrival_bound.md) | `ACCEPTED_V06_FILE` |
| 36 | `implementation/facts/extrapolated_arrival_curve.v` | [extrapolated_arrival_curve facts](files/implementation/facts/2026-09-24_014411_extrapolated_arrival_curve.md) | `ACCEPTED_V06_FILE` |
| 37 | `analysis/definitions/completion_sequence.v` | [completion_sequence](files/analysis/definitions/2026-09-24_031052_completion_sequence.md) | `ACCEPTED_V06_FILE` |
| 38 | `analysis/definitions/finish_time.v` | [finish_time](files/analysis/definitions/2026-09-24_035607_finish_time.md) | `ACCEPTED_V06_FILE` |
| 39 | `analysis/definitions/sbf/average.v` | [average](files/analysis/definitions/sbf/2026-09-24_043858_average.md) | `ACCEPTED_V06_FILE` |
| 40 | `analysis/definitions/sbf/periodic.v` | [periodic](files/analysis/definitions/sbf/2026-09-24_051850_periodic.md) | `ACCEPTED_V06_FILE` |
| 41 | `analysis/definitions/sbf/pred.v` | [pred](files/analysis/definitions/sbf/2026-09-24_053710_pred.md) | `ACCEPTED_V06_FILE` |

## Current proof progress

Machine-published acceptance is now **40 / 357 source files** and **331 / 2439
public declarations**, with **0 translated-but-not-certified in the published
coverage**. The latest completed file is `analysis/definitions/sbf/pred.v`;
it was completed
while `util/lcmseq.v` (rank 30) remained blocked. `util/lcmseq.v`
is still unfinished and its partial
certificate progress does not change accepted coverage.
Machine-readable status/manifest remain the acceptance source; this dashboard
is a human-readable reflection of them.

The formal scheduling document is
[`../v06_file_translation_order.md`](../v06_file_translation_order.md).
Dependency readiness still comes from the accepted file DAG, not from report
text.

## Validation workflow optimization (2026-09-22 11:27:51 +08:00)

The translation skill and workspace validator now make incremental validation
the default for subsequent files. A content-addressed `prepare → check →
finalize` driver binds source, production dependencies, toolchain, exporter /
importer binaries, options, module-loading configuration, and every prepared
output hash. Certificate-only changes reuse verified Lean/export/import
artifacts; relevant input changes generate a different snapshot, while absent
or corrupt cache entries fail closed. Every run records execution count,
cache mode, elapsed time, input fingerprint, and output hashes for all seven
validation stages.

Repeated artifact-local Bool, `eqType`/`DecidableEq`, ordered `seq`/`List`,
roundtrip, and membership proofs can now be generated from one audited Rocq
template. The generated file still names the exact imported artifact and is
kernel-compiled and assumption-audited; this is proof reuse, not a new trust
assumption. Export modes for statement-only types, computation equations,
body projections, guarded normalization, and universe-sensitive datatype
interfaces are also catalogued behind a common config-driven helper.

Regression on existing accepted Sum (25), Poet (1), and Bigcat (13) results
passed without changing their semantic status or acceptance gates. The cold
isolated Lean build took 100.29 s; the identical prepare rerun had four cache
hits, zero stage executions, and took 0.019 s. The final generated-adapter
compile/audit/publication check took 4.24 s. One intentionally retained failed
attempt records an initially ambiguous audit-marker sort and exposed a hook
error-propagation bug; publication remained blocked until both were fixed.

At that original 11:27 workflow-only run, accepted coverage remained **18 / 357
files** and **156 / 2439 declarations**; `util/div_mod.v` was still an
unaccepted 15-declaration Lean candidate. Those numbers are historical context,
not the current dashboard.

### Workflow optimization extension (2026-09-22 21:32:12 +08:00)

The translation skill now requires a whole-file semantic-operation inventory
before freezing a file with more than 20 public declarations. The inventory
must connect every operation to content-addressed certified bridge evidence;
missing support is reported as `missing operation bridge: X`. The adapter
catalog now routes recurring List operations (length/getD/append/filter/head/
last/membership/dedup/index) and Nat operations (order/sub/max) to existing
reusable proof families before any file-specific proof is written.

The incremental state engine can also materialize accepted dependency
`.olean`/imported `.vo` groups from a sealed prepare manifest. It verifies the
producer descriptor and every source/destination hash, and requires the
consumer to bind the reuse evidence; it never infers semantic acceptance from
a copied artifact. A deleted interval-sum bridge and a corrupted imported
`.vo` were both rejected in negative tests.

The Sum/Poet/Bigcat regression was rerun against the current importer
foundation. A stale-foundation `ImportedSubadditivity.vo` was correctly
rejected, so the known workaround was generalized: stable `.out` bytes are
re-imported whenever `LeanImport.Lean` changes. The corrected fresh regression
passed without changing any of the 39 semantic results or gates (106.71 s),
and an identical rerun used four verified prepare-cache hits (1.86 s total).
This extension did not alter production declarations or accepted coverage;
the current project truth remains **21 / 357 files**, **204 / 2439 public
declarations**, and zero translated-but-not-certified declarations before
`behavior/job.v` is published.

### FILE_VALIDATE and stage-recovery extension (2026-09-23)

[The measured workflow report](2026-09-23_091806_validation_file_build_optimization.md)
records a clean Schedule regression, then Service and Supply runs that reused
hash-verified accepted upstream `.olean` modules while fresh-building their
target modules. The observed Lean-build stages fell from 557.660 to 359.290 s
for Service and from 582.154 to 322.633 s for Supply; these are real run
measurements, not controlled speedup guarantees. Exact semantic status and
assumption rows were unchanged. Stage-specific input keys now permit
certificate-only, audit-only, and publication-only retries without rebuilding
Lean or re-exporting; actual Supply probes passed, including cache corruption
rejection. `RECOVER_PREPARE=1` restores sealed successful stages without
mislabeling them `CLEAN_FULL`. Cross-file imported `.vo` reuse and a global
default switch remain **unimplemented**, so the older broad workflow wording
above should not be read as claiming those capabilities.

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
