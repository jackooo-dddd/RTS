# Prosa Translation Source-Provenance History Audit

**Started:** 2026-09-20 10:59:46 HKT  
**Frozen Lean tree:** repository commit `892e0d82b32bfa4de0e542cd9c59720b74ea2a75`  
**Scope:** modern `behavior/`, `util/`, `model/`, `analysis/`, and `results/`; `classic/` excluded.  
**Constraint:** no file under `Prosa-fei/Prosa/` is modified.

## Progress log

### 2026-09-20 10:59:46 HKT — audit initialized

The preceding declaration audit established that pinned Prosa v0.6 is not the uniform source of the frozen Lean tree: several `-- Translated from:` paths are absent in v0.6, declaration groups have moved or split, and the v0.6 `ProcessorState` interface is structurally newer than the Lean class. This audit therefore searches the upstream Prosa Git history for the closest declaration-level fingerprints rather than assuming a release from path names alone.

Evidence dimensions used here are:

- source path at the historical commit, allowing for rename/move/split;
- public declaration names and their order;
- class/record fields and key definition bodies;
- theorem-group overlap;
- per-file Rocq-only and Lean-only declarations;
- consistency of the candidate date/commit across multiple independent files.

Official upstream repository: `https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs.git`. The pinned v0.6 comparison point is commit `414e66760333eaa4ef78c685bcf53291c527a548` (tag `v0.6`).

### 2026-09-20 11:19:25 HKT — tag-wide fingerprint comparison completed

The upstream history was cloned to a validation-only work directory and every modern Lean file's `Translated from` path was compared against tags `v0.4`, `v0.5`, and `v0.6`. The comparison excludes Rocq section-local `Let` declarations and Lean `private` helpers from the public declaration count. “Exact sequence” means the public declaration-name sequence is identical; it does not by itself claim type or semantic equality.

| Candidate | Commit | Commented paths present | Exact declaration-name sequences | Rocq declarations at those paths | Same-name occurrences | Rocq-only by name | Lean-only by name | Ordered LCS |
|---|---|---:|---:|---:|---:|---:|---:|---:|
| **v0.4** | `ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7` | **128 / 128** | **104 / 128** | 783 | **770** | **13** | **38** | **761** |
| v0.5 | `fcdb00b946bc7f6254538ed55694e0c700fc151a` | 122 / 128 | 58 / 128 | 911 | 656 | 255 | 152 | 641 |
| v0.6 | `414e66760333eaa4ef78c685bcf53291c527a548` | 102 / 128 | 37 / 128 | 862 | 535 | 327 | 273 | 519 |

The v0.4 result is decisive at the version level:

- every one of the 128 modern Lean `Translated from` paths exists at v0.4;
- 104 files have exactly the same public declaration-name order;
- 770 of 783 v0.4 public declarations at the referenced paths have a same-name Lean declaration (98.3%);
- the 13 name-unmatched source declarations consist of 11 declarations omitted from current `Analysis/Facts/Transform/Edf_opt.lean` plus `util/seqset.v`'s carrier/eq-mixin names, which are reformulated as Lean `SeqSet` and typeclass instances;
- the 38 name-unmatched Lean declarations are predominantly explicit computational helpers, promoted source-local `Let` aliases, and representation names such as `SeqSet`.

The v0.4 Rocq-only/Lean-only counts are therefore not 13 translation failures plus 38 arbitrary extras. Manual resolution identifies the `set`/`set_eqMixin` ↔ `SeqSet`/instances representation change, the source-derived `scheduled_in` extraction, explicit encodings of notations, source-local aliases promoted into Lean definitions, and proof-support helpers. The only remaining public-name coverage cluster requiring an original-translation warning is the 11-item `Edf_opt` group.

In contrast, by v0.6, 26 of the commented paths no longer exist and only 37 files preserve the same public declaration-name sequence. No path-remapping hypothesis is needed to explain the v0.4 tree.

#### Exact-commit resolution

The strongest commit hypothesis is the v0.4 release commit:

```text
ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7
tag: v0.4
date: 2019-12-21
```

The artifacts do not uniquely distinguish that tag from the next two compatibility-only commits:

```text
aae959e6456b54637f34faec63d021c170174d4d  2020-01-21  Compile with mathcomp 1.10
12f79735364abc04302929bfa86a35a308e15bc1  2020-01-23  Compile with coq dev
```

Those commits do not introduce the declaration/signature fingerprints used here. The next relevant change is `7dc8adcc712acd53dd3ac8fe47ae5af42265e4ee` on 2020-02-10, which restructures `util/bigcat.v`. Current Lean theorem binder order matches the pre-restructure v0.4 form: each theorem takes `f` explicitly in the old position, rather than inheriting the later section-level `f`. The related 2020-02-10 work-conservation change also introduces three service facts absent from Lean. Therefore the most honest exact provenance statement is:

> **High-confidence version:** Prosa v0.4.  
> **Best single-commit hypothesis:** `ee05f255...` (the v0.4 tag).  
> **Indistinguishable source window:** `ee05f255...` through `12f79735...`, before 2020-02-10.

No positive evidence requires multiple source versions. Some individual files are unchanged across several releases and hence have low standalone dating power, but their paths and declarations are fully consistent with the single v0.4 snapshot selected by the discriminating files.

#### High-value file fingerprints

| Lean file | v0.4 comparison | Later-version comparison | Provenance conclusion |
|---|---|---|---|
| `Behavior/Schedule.lean` | v0.4 has external `State`, `Core`, `scheduled_on`, derived `scheduled_in`, primitive aggregate `service_in`, and `service_implies_scheduled` | per-core `service_on` appears in 2021; `State` moves into the class in 2022; supply appears in 2023 | **v0.4, high confidence** |
| `Behavior/Service.lean` | all 11 public names match exactly; old `completes_at` has no zero-time disjunct | `receives_service_at` appears in 2021; zero-time fix appears in 2025 | **v0.4, high confidence** |
| `Model/Task/Concept.lean` | all 12 public names match exactly | `TaskMinCost` family appears in 2020; same-task remarks in 2023 | **v0.4, high confidence** |
| `Util/Sum.lean` | all 14 v0.4 source names occur in order; two extra Lean proof helpers | only 9 names overlap v0.5 and 7 overlap v0.6 | **v0.4, high confidence** |
| `Analysis/Facts/Busy_interval/Priority_inversion.lean` | all 24 v0.4 names occur; ordered LCS 23 due to one reordering | old group is split/moved and eventually the old path disappears | **v0.4, high confidence** |
| `Analysis/Facts/Model/Ideal_schedule.lean` | all 10 names match in exact order | old path removed/renamed in 2022; newer file gains supply/service facts | **v0.4, high confidence** |
| `Results/Edf/Rta/Bounded_pi.lean` | all 17 public v0.4 names occur; three Lean definitions lift/rename source-local aliases | theorem group evolves and results hierarchy is later reorganized | **v0.4, high confidence** |
| `Results/Fixed_priority/Rta/Bounded_pi.lean` | all 7 public v0.4 names occur; two Lean definitions lift local work-conservation aliases | later RTA structure diverges and moves | **v0.4, high confidence** |

For EDF bounded PI, the three apparent Lean extras are not unrelated inventions: `bound_on_total_hep_workload` and `total_interference_bound_fn` correspond to source-local `Let` definitions, while `is_in_search_space_edf` is the source-local `is_in_search_space` with a disambiguating name. The analogous FP helpers `work_conserving_ab` and `work_conserving_cl` also lift v0.4 local aliases.

#### Requested anomaly reclassification

| Item | Classification | Evidence |
|---|---|---|
| `ProcessorState` | `SOURCE_VERSION_DRIFT` | Lean matches the v0.4 abstraction; v0.6's per-core service/supply interface is later evolution. |
| `completes_at` | `SOURCE_VERSION_DRIFT` | Lean matches v0.4. The `t = 0` disjunct was added by the 2025-02-28 source fix `00a1ec28...`. |
| `TaskMinCost` and minimum-cost validity chain | `LATER_PROSA_ADDITION` | introduced by `e33a1ebe...` on 2020-09-22. |
| `receives_service_at` | `LATER_PROSA_ADDITION` | introduced by `3f3fac41...` on 2021-03-01. |
| `arrivals_between_P` | `LATER_PROSA_ADDITION` | introduced by `a5637158...` on 2020-08-10. |
| Lean `sum0`, `sum_diff`, `sum_majorant_eqn`, `sum_notin_rem_eqn`, `sum_pred_diff`, `sum_seq_diff`, `sum_seq_gt0P` | `SOURCE_VERSION_DRIFT` | all are genuine v0.4 `util/sum.v` source declarations. |
| Lean `list_sum_map_add`, `list_mem_le_ite_sum` | `LEAN_HELPER` | absent as source declarations and used to support Lean proofs. |
| v0.6-only `util/sum`, `util/list`, and `util/bigcat` declarations | `LATER_PROSA_ADDITION` | v0.4 declaration groups align closely with Lean; additions appear later in history. |
| old `priority_inversion.v`, `ideal_schedule.v`, `job_properties.v`, and results layouts | `FILE_MOVE_OR_SPLIT` | current Lean matches the old v0.4 groups; later Prosa reorganizes them. |
| later RBF and supply/service facts | `LATER_PROSA_ADDITION` | the v0.4 files' public declaration sets are represented; the larger theorem families accumulate afterward. |
| 11 v0.4 declarations absent from current `Edf_opt.lean` | `LIKELY_ORIGINAL_TRANSLATION_MISMATCH` | these are already present in the likely original source and remain absent from current Lean. |
| exact commit within the three-commit v0.4-compatible window | `UNRESOLVED_PROVENANCE` | declarations and relevant signatures cannot distinguish the release tag from two compatibility-only successors. |

The prior `JobType`, `SeqSet`, and `ideal_is_idle` rows are not forced into a failure class: they are representation/name reformulations with a clear v0.4 source, not unresolved provenance and not demonstrated semantic mismatches.

The 11 `Edf_opt` public names are `t1_relevant`, `fsc_search_successful`, `scheduled_job_in_sched_has_later_deadline`, `mea_scheduled_job_has_later_deadline`, `mea_guarantee_dl_orig`, `mea_guarantee_fsc_is_j_edf`, `mea_guarantee_deadlines`, `mea_guarantee_case_t'_past_deadline`, `mea_guarantee_case_t'_before_deadline`, `edf_transform_jobs_come_from_arrival_sequence`, and `edf_schedule_meets_all_deadlines`. This is a declaration-level 1:1 coverage warning, not yet a proof of semantic error: several facts are visibly inlined into `fsc_search_result` or `make_edf_at_guarantee`, two use the more general `scheduled_at_implies_later_deadline`, and final theorems bypass some intermediate named lemmas. They remain `LIKELY_ORIGINAL_TRANSLATION_MISMATCH` because the public source declarations themselves have no 1:1 Lean declarations.

The grouped machine-readable reclassification is in `reports/logs/prosa_source_provenance_2026-09-20/provenance_reclassification.csv`. A second table, `prior_anomalies_reclassified.csv`, assigns a history-based result to each of the 37 curated rows from the preceding declaration audit. It adds `REPRESENTATION_REFORMULATION` for `JobType` and `SeqSet`, because forcing known representation changes into a mismatch or unresolved-provenance category would be misleading.

#### Important correction to the prior v0.6 audit interpretation

The v0.6-based semantic findings remain technically valid **as comparisons against v0.6**, but they do not all diagnose errors in the original translation:

- the `completes_at` zero-time counterexample proves current Lean differs from v0.6, while history shows current Lean faithfully reflects the older v0.4 statement;
- the current `ProcessorState` cannot validate against v0.6's per-core supply/service interface because that interface did not exist in the apparent source snapshot;
- missing `TaskMinCost` and `receives_service_at` are later-source coverage gaps, not original omissions;
- `util/sum` declarations previously labeled “Lean-only relative to v0.6” are in fact direct v0.4 source declarations.

Thus, future reports should label certificates against v0.6 as **cross-version conformance checks**, not automatically as validation of the historical translation source.

#### Remaining provenance uncertainty

- **Exact commit:** unresolved within the three-commit v0.4-compatible window stated above.
- **Individually weak fingerprints:** files such as `behavior/time.v` and `analysis/facts/tdma.v` retain the same names across later tags; they are dated by the surrounding tree, not by unique local changes.
- **Representation-heavy files:** `util/notation.v` and `util/seqset.v` require notation/typeclass-aware matching rather than name counts, but both paths and surrounding declaration groups agree with v0.4.
- **No mixed-version evidence:** no Lean file requires a post-v0.4 declaration to explain its public API. Lean-only helpers are implementation artifacts, not evidence of a second Rocq snapshot.

### 2026-09-20 11:24:39 HKT — final reproducibility and integrity checks

Representative commands:

```bash
git clone --filter=blob:none --no-checkout \
  https://gitlab.mpi-sws.org/RT-PROOFS/rt-proofs.git \
  Validation/.work/prosa_history_repo

python3 Validation/scripts/audit_prosa_history_provenance.py \
  --history-repo Validation/.work/prosa_history_repo \
  --lean-root Prosa \
  --revision v0.4 --revision v0.5 --revision v0.6 \
  --output Validation/reports/logs/prosa_source_provenance_2026-09-20/tag_fingerprints.json

git -C Validation/.work/prosa_history_repo log -S'TaskMinCost' -- model/task/concept.v
git -C Validation/.work/prosa_history_repo log -S'receives_service_at' -- behavior/service.v
git -C Validation/.work/prosa_history_repo log -S't == 0' -- behavior/service.v
git -C Validation/.work/prosa_history_repo log --follow -- analysis/facts/model/ideal_schedule.v
```

Generated evidence:

- `tag_fingerprints.json` / `.csv`: all 128 files against v0.4, v0.5, and v0.6;
- `early_2020_fingerprints.json` / `.csv`: v0.4 and six early-2020 boundary commits;
- `provenance_reclassification.csv`: grouped high-value findings;
- `prior_anomalies_reclassified.csv`: all 37 preceding curated anomalies reclassified individually.

Final checks:

```text
history-audit script syntax: PASS
tag-fingerprint assertions: PASS
37-row prior-anomaly classification parses: PASS
git diff --check: PASS
production Prosa/ diff: empty
translation files modified: none
```

## Final source-version hypothesis

The frozen modern Lean translation is best understood as a translation of **Prosa v0.4**, most likely tag commit `ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7`, rather than Prosa v0.6. The exact source checkout could instead be either of the two immediately following compatibility commits through `12f79735364abc04302929bfa86a35a308e15bc1`; available declarations and signatures do not distinguish them. The source is definitively older than the 2020-02-10 `util/bigcat.v` restructuring.

There is no evidence that the modern Lean tree mixes multiple Prosa source releases. The apparent mixture is explained by later Prosa evolution, file moves/splits, explicit Lean helpers, and a small number of source declarations whose proofs/facts were inlined instead of retained as 1:1 public Lean declarations.
