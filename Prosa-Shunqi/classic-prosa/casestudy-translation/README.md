# Classic Prosa → Lean: case-study translation

<!-- STATUS_BEGIN -->
**Progress: 0 / 49 classic files accepted** (40 translated, 0 in progress, 8 deferred, 0 blocked) ·
tier S 38 files · tier P 11 files · v0.6 `util` dependencies: 14 / 14 already accepted ·
next file: **rank 49** `classic/analysis/global/basic/bertogna_edf_theory.v` · last update: 2026-10-01
<!-- STATUS_END -->

Goal: translate exactly the Classic Prosa files needed for the 22 `RTS_Papers` case studies, so
that their statements can be written in Lean and later proved there.

## Source authority

- **The only source is ProsaBuddy's classic Prosa**: repository `prosabuddy` at commit
  `f692cb7479780cf6009493f373a309e13165201c` (clean tree), directory
  `prosabuddy/prosaworkspace/classic/`. This is the copy ProsaBuddy's own case-study build
  (`prosaworkspace/Makefile.case2015`, `-R . prosa`) compiles, and the environment in which the
  case-study theorems will be proved.
  - Every file is bound by its sha256 in [`file_order.csv`](file_order.csv). A hash mismatch
    means the source changed: stop and re-plan.
  - ProsaBuddy's second copy, `prosaworkspace/rt-proofs-v0.6/classic/`, is **not** used. In
    scope it differs only in proof scripts of ranks 36 and 47.
  - It is the Prosa v0.4 classic, ported by ProsaBuddy to Rocq 9.x and MathComp 2.x; statements
    are unchanged from v0.4 except 8 compatibility renames, none in scope. Not the 2022
    `classic-prosa` branch head in `../classic/`, which is kept for reference only.
- **Rocq reference build** in this project's validation environment (Rocq 9.3+rc1 +
  MathComp 2.6): [`../rocq93-port/`](../rocq93-port/). All 49 files in scope compile there
  unmodified, with the prelude `Rocq90Compat.v`. All in-scope theorems are axiom-free and their
  statements are identical to ProsaBuddy's Rocq 9.0 build. See `../TRANSLATION_ASSESSMENT.md`
  §8.
- **v0.6 `util`**: classic imports 14 official v0.6 `util` modules. They are byte-identical to
  this project's pinned v0.6, so the already accepted Lean modules `Prosa.Util.*` are reused,
  not re-translated.

## Scope and ranking

49 classic files, 525 declarations (275 used by the case studies or their classic proof
support), 12.9k lines.

- **Tier S (38 files):** needed to *state* the case studies.
- **Tier P (11 files):** classic analysis files supporting their proofs, i.e. Bertogna–Cirinei
  workload/interference bounds and RTAs (global FP/EDF, APA FP).
- **Ranks** form a topological order of the file dependency graph
  ([`file_dependencies.csv`](file_dependencies.csv)). Within a layer, tier S comes before tier
  P, then files are ordered by path. A file is **READY** when all its dependencies are ACCEPTED.
- ¹ These files are in scope only because the case studies import `classic/util/all.v`, which
  re-exports every classic utility. None of their declarations is used by the case studies:
  translate them last within their layer, or mark them DEFERRED with a note.

**Statuses:** `TODO` → `IN_PROGRESS` → `TRANSLATED` (Lean compiles, no `sorry`/axioms) →
`ACCEPTED` (validated against the Rocq reference). `BLOCKED` and `DEFERRED` always carry a
note. Keep the table below and `file_order.csv` in sync.

| Rank | Layer | Tier | ProsaBuddy source (`classic/…`) | Decls (used) | Lines | Lean target (`Prosa/Classic/…`) | Status |
|---:|---:|:---:|---|---:|---:|---|---|
| 1 | 0 | S | `model/time.v` | 3 (1) | 8 | `Model/Time.lean` | TRANSLATED |
| 2 | 0 | S | `util/pick.v` ¹ | 17 (0) | 291 | `Util/Pick.lean` | DEFERRED |
| 3 | 0 | S | `util/ssromega.v` ¹ | 0 (0) | 31 | `Util/Ssromega.lean` | DEFERRED |
| 4 | 1 | S | `util/notation.v` | 6 (1) | 81 | `Util/Notation.lean` | TRANSLATED |
| 5 | 1 | S | `util/seqset.v` | 2 (1) | 29 | `Util/Seqset.lean` | TRANSLATED |
| 6 | 1 | S | `util/tactics.v` ¹ | 13 (0) | 384 | `Util/Tactics.lean` | DEFERRED |
| 7 | 2 | S | `util/bigord.v` | 4 (4) | 41 | `Util/Bigord.lean` | TRANSLATED |
| 8 | 2 | S | `util/induction.v` | 2 (1) | 31 | `Util/Induction.lean` | TRANSLATED |
| 9 | 2 | S | `util/list.v` | 44 (2) | 787 | `Util/List.lean` | TRANSLATED |
| 10 | 2 | S | `util/nat.v` | 8 (5) | 80 | `Util/Nat.lean` | TRANSLATED |
| 11 | 2 | S | `util/ord_quantifier.v` | 4 (2) | 101 | `Util/OrdQuantifier.lean` | TRANSLATED |
| 12 | 2 | S | `util/powerset.v` ¹ | 2 (0) | 19 | `Util/Powerset.lean` | DEFERRED |
| 13 | 3 | S | `util/bigcat.v` | 6 (5) | 103 | `Util/Bigcat.lean` | TRANSLATED |
| 14 | 3 | S | `util/counting.v` | 5 (5) | 104 | `Util/Counting.lean` | TRANSLATED |
| 15 | 3 | S | `util/div_mod.v` | 17 (4) | 237 | `Util/DivMod.lean` | TRANSLATED |
| 16 | 3 | S | `util/fixedpoint.v` ¹ | 10 (0) | 191 | `Util/Fixedpoint.lean` | DEFERRED |
| 17 | 3 | S | `util/sorting.v` | 6 (1) | 161 | `Util/Sorting.lean` | TRANSLATED |
| 18 | 3 | S | `util/step_function.v` ¹ | 0 (0) | 3 | `Util/StepFunction.lean` | DEFERRED |
| 19 | 4 | S | `util/minmax.v` ¹ | 44 (0) | 544 | `Util/Minmax.lean` | DEFERRED |
| 20 | 4 | S | `util/sum.v` | 9 (6) | 185 | `Util/Sum.lean` | TRANSLATED |
| 21 | 5 | S | `util/all.v` ¹ | 0 (0) | 21 | `Util/All.lean` | DEFERRED |
| 22 | 6 | S | `model/arrival/basic/task.v` | 11 (9) | 82 | `Model/Arrival/Basic/Task.lean` | TRANSLATED |
| 23 | 7 | S | `model/arrival/basic/arrival_sequence.v` | 20 (9) | 232 | `Model/Arrival/Basic/ArrivalSequence.lean` | TRANSLATED |
| 24 | 8 | S | `model/arrival/basic/job.v` | 8 (7) | 94 | `Model/Arrival/Basic/Job.lean` | TRANSLATED |
| 25 | 9 | S | `model/arrival/basic/task_arrival.v` | 11 (3) | 236 | `Model/Arrival/Basic/TaskArrival.lean` | TRANSLATED |
| 26 | 9 | S | `model/priority.v` | 35 (10) | 356 | `Model/Priority.lean` | TRANSLATED |
| 27 | 9 | S | `model/schedule/global/basic/schedule.v` | 39 (34) | 616 | `Model/Schedule/Global/Basic/Schedule.lean` | TRANSLATED |
| 28 | 10 | S | `model/arrival/basic/arrival_bounds.v` | 10 (0) | 226 | `Model/Arrival/Basic/ArrivalBounds.lean` | TRANSLATED |
| 29 | 10 | S | `model/schedule/apa/affinity.v` | 7 (7) | 102 | `Model/Schedule/Apa/Affinity.lean` | TRANSLATED |
| 30 | 10 | S | `model/schedule/global/response_time.v` | 5 (3) | 135 | `Model/Schedule/Global/ResponseTime.lean` | TRANSLATED |
| 31 | 10 | S | `model/schedule/global/schedulability.v` | 7 (2) | 172 | `Model/Schedule/Global/Schedulability.lean` | TRANSLATED |
| 32 | 11 | S | `model/schedule/global/workload.v` | 4 (4) | 97 | `Model/Schedule/Global/Workload.lean` | TRANSLATED |
| 33 | 12 | S | `model/schedule/apa/interference.v` | 11 (4) | 272 | `Model/Schedule/Apa/Interference.lean` | TRANSLATED |
| 34 | 12 | S | `model/schedule/global/basic/interference.v` | 9 (8) | 205 | `Model/Schedule/Global/Basic/Interference.lean` | TRANSLATED |
| 35 | 12 | P | `analysis/apa/workload_bound.v` | 21 (20) | 744 | `Analysis/Apa/WorkloadBound.lean` | TRANSLATED |
| 36 | 12 | P | `analysis/global/basic/workload_bound.v` | 21 (20) | 743 | `Analysis/Global/Basic/WorkloadBound.lean` | TRANSLATED |
| 37 | 13 | S | `model/schedule/apa/platform.v` | 5 (3) | 116 | `Model/Schedule/Apa/Platform.lean` | TRANSLATED |
| 38 | 13 | S | `model/schedule/global/basic/platform.v` | 6 (6) | 189 | `Model/Schedule/Global/Basic/Platform.lean` | TRANSLATED |
| 39 | 13 | P | `analysis/apa/interference_bound.v` | 1 (1) | 45 | `Analysis/Apa/InterferenceBound.lean` | TRANSLATED |
| 40 | 13 | P | `analysis/global/basic/interference_bound.v` | 1 (1) | 43 | `Analysis/Global/Basic/InterferenceBound.lean` | TRANSLATED |
| 41 | 14 | S | `model/schedule/apa/constrained_deadlines.v` | 4 (3) | 288 | `Model/Schedule/Apa/ConstrainedDeadlines.lean` | TRANSLATED |
| 42 | 14 | S | `model/schedule/global/basic/constrained_deadlines.v` | 6 (6) | 443 | `Model/Schedule/Global/Basic/ConstrainedDeadlines.lean` | TRANSLATED |
| 43 | 14 | P | `analysis/apa/interference_bound_fp.v` | 1 (1) | 56 | `Analysis/Apa/InterferenceBoundFp.lean` | TRANSLATED |
| 44 | 14 | P | `analysis/global/basic/interference_bound_fp.v` | 1 (1) | 46 | `Analysis/Global/Basic/InterferenceBoundFp.lean` | TRANSLATED |
| 45 | 14 | P | `model/schedule/global/basic/interference_edf.v` | 1 (1) | 72 | `Model/Schedule/Global/Basic/InterferenceEdf.lean` | TRANSLATED |
| 46 | 15 | P | `analysis/apa/bertogna_fp_theory.v` | 13 (13) | 1049 | `Analysis/Apa/BertognaFpTheory.lean` | TRANSLATED |
| 47 | 15 | P | `analysis/global/basic/bertogna_fp_theory.v` | 10 (10) | 788 | `Analysis/Global/Basic/BertognaFpTheory.lean` | TRANSLATED |
| 48 | 15 | P | `analysis/global/basic/interference_bound_edf.v` | 41 (37) | 1200 | `Analysis/Global/Basic/InterferenceBoundEdf.lean` | TRANSLATED |
| 49 | 16 | P | `analysis/global/basic/bertogna_edf_theory.v` | 14 (14) | 821 | `Analysis/Global/Basic/BertognaEdfTheory.lean` | TODO |

### Already available (v0.6 `util`, accepted in this project)

| v0.6 source | Lean module | Status |
|---|---|---|
| `util/bigcat.v` | `Prosa.Util.Bigcat` (`Prosa/Util/Bigcat.lean`) | DONE (v0.6 accepted) |
| `util/div_mod.v` | `Prosa.Util.Div_mod` (`Prosa/Util/Div_mod.lean`) | DONE (v0.6 accepted) |
| `util/epsilon.v` | `Prosa.Util.Epsilon` (`Prosa/Util/Epsilon.lean`) | DONE (v0.6 accepted) |
| `util/list.v` | `Prosa.Util.List` (`Prosa/Util/List.lean`) | DONE (v0.6 accepted) |
| `util/minmax.v` | `Prosa.Util.Minmax` (`Prosa/Util/Minmax.lean`) | DONE (v0.6 accepted) |
| `util/nat.v` | `Prosa.Util.Nat` (`Prosa/Util/Nat.lean`) | DONE (v0.6 accepted) |
| `util/notation.v` | `Prosa.Util.Notation` (`Prosa/Util/Notation.lean`) | DONE (v0.6 accepted) |
| `util/rel.v` | `Prosa.Util.Rel` (`Prosa/Util/Rel.lean`) | DONE (v0.6 accepted) |
| `util/seqset.v` | `Prosa.Util.Seqset` (`Prosa/Util/Seqset.lean`) | DONE (v0.6 accepted) |
| `util/setoid.v` | `Prosa.Util.Setoid` (`Prosa/Util/Setoid.lean`) | DONE (v0.6 accepted) |
| `util/subadditivity.v` | `Prosa.Util.Subadditivity` (`Prosa/Util/Subadditivity.lean`) | DONE (v0.6 accepted) |
| `util/sum.v` | `Prosa.Util.Sum` (`Prosa/Util/Sum.lean`) | DONE (v0.6 accepted) |
| `util/supremum.v` | `Prosa.Util.Supremum` (`Prosa/Util/Supremum.lean`) | DONE (v0.6 accepted) |
| `util/tactics.v` | `Prosa.Util.Tactics` (`Prosa/Util/Tactics.lean`) | DONE (v0.6 accepted) |

## Case studies

All 22 case-study statements become writable once ranks 1–42 are accepted: after rank 38 for
2009-RTSS-Lemma5, 2009-RTSS-Theorem2 and 2014-RTCSA-Lemma4, and after rank 41 for
2015-RTAS-Lemma8. See [`case_studies.csv`](case_studies.csv).

| Case studies | Classic proof support | Ranks |
|---|---|---|
| 2007-RTSS-Theorem2 | `task_interference_le_workload` (direct counterpart) | 34 |
| 2007-RTSS-Theorem4 | `workload_bounded_by_W` (direct counterpart) | 36 |
| 2015-RTAS-Lemma8 | APA `bertogna_cirinei_response_time_bound_fp` (direct counterpart) | 35, 39, 43, 46 |
| 2005-ECRTS Lemma3/Lemma4/Theorem6 | global EDF Bertogna–Cirinei proof steps | 36, 40, 45, 48, 49 |
| 2007-RTSS-Theorem3 | global FP Bertogna–Cirinei proof steps | 36, 40, 44, 47 |
| 2009-RTSS (11), 2014-RTCSA (3), 2015-BOOK-Lemma18.1 | none in classic: new proofs on the FP infrastructure | 36, 47 |

The case-study files also contain their own local definitions (105 names, 133 distinct
variants across files). Translate those together with each case study, after rank 42.

## Procedure

### Stage 0: prerequisites (pending your approval)

1. **Validation pipeline.** `Validation/scripts/translation_file_pipeline.py` is pinned to v0.6
   (`SOURCE_ROOT = .work/prosa-v06-414e667`, `PIN = 414e667…`). Classic validation needs:
   - a classic source root (ProsaBuddy `f692cb7`, hashes as in `file_order.csv`);
   - the build of `../rocq93-port/` with the prelude flags
     `-Q <compat> Compat -ri Compat.Rocq90Compat`;
   - a separate status chain, so v0.6 coverage numbers stay unaffected.

   Do not edit the pipeline while v0.6 runs are active.
2. **Representation addendum** for classic, extending
   `Validation/planning/v06_current_policy/representation_policy.md` (decide at the rank where
   each item first appears):
   - `Context {T : eqType}` → carrier + `[DecidableEq T]`, as in v0.6 (rank 1 onwards);
   - classic passes model parameters as **explicit functions** (`job_cost : Job → time`, …).
     Keep them explicit, not type classes, so statements stay identical to ProsaBuddy's
     (rank 22 onwards);
   - `time := nat` (rank 1); `seq` → `List`, `bool` stays `Bool`, as in v0.6;
   - global schedules: `schedule Job num_cpus`, with processors as ordinals
     `'I_num_cpus` → `Fin num_cpus` (rank 27); APA affinities (rank 29);
   - Ltac-only files (`ssromega.v`, most of `tactics.v`) have no Lean declarations; Lean
     proofs use `omega`/`simp`.
3. **Skill addendum**: the `prosa-v06-translation` skill names v0.6 as its only authority. Add
   a classic section pointing to this README before agents translate classic files.

### Per-file loop (same discipline as v0.6)

1. Take the lowest-rank `TODO` file that is READY. Check that its sha256 still matches
   `file_order.csv`.
2. Write the declaration contract from the ProsaBuddy source and the elaborated types in the
   Rocq 9.3 reference build: full names, section variables and hypotheses after closing,
   definition bodies, notations and implicit arguments.
3. Translate to `Prosa/Classic/…` (target in the table), namespace = module path. Reuse
   `Prosa.Util.*` and earlier classic translations; do not re-translate.
4. Compile; no `sorry`, no new axioms; check with `#print axioms`. Set the status to
   `TRANSLATED`.
5. Validate against the Rocq reference once Stage 0 is in place. Set `ACCEPTED`.
6. Update this table, the status block at the top, `file_order.csv`, and the file's report in
   `reports/` (one per source file).

### Lean naming

Each path segment goes snake_case → UpperCamelCase:
`classic/model/schedule/global/basic/schedule.v` →
`Prosa/Classic/Model/Schedule/Global/Basic/Schedule.lean`, namespace
`Prosa.Classic.Model.Schedule.Global.Basic.Schedule`. Rename any segment that is a reserved
Lean file name (e.g. `Aux`) and note it in the report.

## Change log

- 2026-10-01: plan created (scope, ranks, hashes, Rocq 9.3 reference build). No files
  translated yet.
