# Classic Prosa → Lean: comprehensive translation

<!-- STATUS_BEGIN -->
**Progress: 141 / 141 remaining classic files translated** (+ 49 reused from the case studies; ACCEPTED 190) · last update: 2026-10-04
<!-- STATUS_END -->

Goal: translate **the whole classic Prosa folder** of ProsaBuddy to Lean 4 over this project's Lean Prosa,
not only the 49 files the `RTS_Papers` case studies need
([`../casestudy-translation/`](../casestudy-translation/)).

## Source authority

- Same source as the case-study translation: repository `prosabuddy`, commit
  `f692cb7479780cf6009493f373a309e13165201c`, directory `prosaworkspace/classic/` (pinned checkout
  `Validation/.work/prosabuddy-f692cb7`, never edited). It is Prosa v0.4's classic part, ported by ProsaBuddy
  to Rocq 9.x and MathComp 2.x. Every file is bound by its sha256 in [`file_order.csv`](file_order.csv).
- 190 classic `.v` files, all listed in ProsaBuddy's full build (`Makefile.prosaworkspace_all.conf`).
  A trial build of all of them in ProsaBuddy's own toolchain (opam switch `prosa-0.6`, Rocq 9.0.1,
  MathComp 2.4) is in `Validation/.work/classic_full_probe_rocq90/`; files that do not compile there are
  marked in the notes.
- Classic files import 12 official v0.6 `util` modules. They are byte-identical to this project's pinned v0.6,
  so the accepted Lean modules `Prosa.Util.*` are reused, as in the case-study translation.

## Scope and order

- **190 classic files.** 49 were translated (and validated) for the case studies; they keep their Lean
  modules and are reused, not re-translated (marked ᶜ in the table). **141 files remain** (about 47k lines).
- [`file_dependencies.csv`](file_dependencies.csv): every direct `Require` edge (classic → classic, classic →
  v0.6 `util`), parsed from the sources.
- [`file_order.csv`](file_order.csv): the translation order. Ranks are a topological order of the dependency
  graph. The **layer** of a file is the length of its longest chain of classic dependencies. Within a layer,
  files are ordered by area (`util`, `model`, `analysis`, `implementation`), then by path, so related files
  (e.g. one family of jitter or suspension files) stay together. A file is **READY** when all its classic
  dependencies are TRANSLATED or ACCEPTED.
- `decls` is the exact number of declarations: from the case-study inventory for reused files, otherwise from the `Print Module` contract of the trial build (`contracts/<file>.txt`, written by `dump_contracts.py`).
  (2026-10-03: fixed a `dump_contracts.py` parsing bug that dropped the declaration directly following a module
  alias or collapsed submodule, e.g. `never_migrates` in `model/schedule/partitioned/schedule.v`; the 11 affected
  contracts, all still `TODO`, were re-dumped.)
- `python3 make_plan.py` regenerates both CSV files and the table below, keeping existing statuses.

## How files are translated

- Lean target: `Prosa/Classic/<Path in CamelCase>.lean`; namespace = file path + Rocq `Module` name, as in
  the case-study translation (`classic/model/schedule/uni/schedule.v` → `Prosa.Classic.Model.Schedule.Uni.Schedule`).
- Same conventions as the case-study translation: same declaration names, binders, order and implicitness as
  the elaborated Rocq statements; the classic representation addendum
  (`Validation/planning/classic_policy/representation_addendum.md`) for Boolean/Prop, sums, sequences,
  `\cat`, `sort`, and Rocq `Section` variables; Rocq `Let`s unfolded or kept as `LEAN_HELPER` definitions.
- Rocq `Inductive` types become Lean `inductive` types with the same constructors; Rocq's auto-generated
  eliminators (`_rect`, `_ind`, `_rec`, `_sind`) correspond to Lean's auto-generated `rec`/`recOn`/`casesOn`
  and are not restated.
- MathComp `transitive R` is inlined as `∀ y x z, R x y = true → R y z = true → R x z = true` and `total R` as
  `∀ x y, (R x y || R y x) = true`; `predT` is `fun _ => true`.
- Every translated file compiles, has complete proofs (no `sorry`, no new axioms), and
  `#print axioms` of its declarations lists only `propext`, `Classical.choice`, `Quot.sound`.
- Concrete examples in `implementation/` (task sets, schedules, response-time computations) are translated
  as definitions plus the same theorems; proofs by computation use `decide`/`rfl` (never `native_decide`).

**Checking:** `python3 check_translated.py` builds every `TRANSLATED` target, rejects `sorry`/`admit`, and uses
Lean's `collectAxioms` on every declaration of those modules (only `propext`, `Classical.choice`, `Quot.sound`
allowed). `python3 check_binders.py` compares, for every declaration of every `TRANSLATED` file, the Lean binder
names (explicit/implicit, in order) with the Rocq contract's `Arguments` line (documented exclusions: Rocq
eliminators, Hierarchy-Builder artifacts, structure fields matched by name, a Lean `x0` for a repeated Rocq binder
`x`). `TRANSLATED` is not `ACCEPTED`: the classic validation family (Rocq-reference comparison) has not been
run on these files yet.

**Statuses:** `TODO` → `IN_PROGRESS` → `TRANSLATED` (Lean compiles, complete proofs) → `ACCEPTED`
(validated against the Rocq reference with the classic validation family). `BLOCKED` and `DEFERRED` always
carry a note in `file_order.csv`.

## Translation corrections

- 2026-10-03 — ranks 134 (`implementation/apa/schedule.v`), 135 (`implementation/global/basic/schedule.v`) and 152
  (`implementation/global/jitter/schedule.v`): these schedulers sort the pending jobs with MathComp's `sort` by an
  *arbitrary* JLDP relation. The earlier translation used `List.mergeSort`, which coincides with MathComp's `sort` only
  for total, transitive relations, so the definitions were not faithful for every input. Each of the three Lean files
  now restates MathComp's merge sort equation by equation (`mc_merge_s1`, `mc_merge`, `mc_merge_sort_push`,
  `mc_merge_sort_pop`, `mc_merge_sort_rec`, `mc_sort`; structurally recursive `LEAN_HELPER` definitions) with the
  permutation and sortedness facts used by the proofs (`mc_sort_perm`, `mem_mc_sort`, `pairwise_mc_sort`). The
  validation relates `sort` and `mc_sort` for every relation.

## Files

<!-- TABLE_BEGIN -->
| Rank | Layer | ProsaBuddy source (`classic/…`) | Decls | Lines | Lean target (`Prosa/Classic/…`) | Status |
|---:|---:|---|---:|---:|---|---|
| 1 | 0 | `util/notation.v` ᶜ | 6 | 80 | `Util/Notation.lean` | ACCEPTED |
| 2 | 0 | `util/pick.v` ᶜ | 17 | 290 | `Util/Pick.lean` | ACCEPTED |
| 3 | 0 | `util/seqset.v` ᶜ | 2 | 28 | `Util/Seqset.lean` | ACCEPTED |
| 4 | 0 | `util/ssromega.v` ᶜ | 0 | 30 | `Util/Ssromega.lean` | ACCEPTED |
| 5 | 0 | `util/tactics.v` ᶜ | 13 | 383 | `Util/Tactics.lean` | ACCEPTED |
| 6 | 0 | `model/time.v` ᶜ | 3 | 7 | `Model/Time.lean` | ACCEPTED |
| 7 | 1 | `util/bigord.v` ᶜ | 4 | 40 | `Util/Bigord.lean` | ACCEPTED |
| 8 | 1 | `util/induction.v` ᶜ | 2 | 30 | `Util/Induction.lean` | ACCEPTED |
| 9 | 1 | `util/list.v` ᶜ | 44 | 786 | `Util/List.lean` | ACCEPTED |
| 10 | 1 | `util/nat.v` ᶜ | 8 | 79 | `Util/Nat.lean` | ACCEPTED |
| 11 | 1 | `util/ord_quantifier.v` ᶜ | 4 | 100 | `Util/OrdQuantifier.lean` | ACCEPTED |
| 12 | 1 | `util/powerset.v` ᶜ | 2 | 18 | `Util/Powerset.lean` | ACCEPTED |
| 13 | 2 | `util/bigcat.v` ᶜ | 6 | 102 | `Util/Bigcat.lean` | ACCEPTED |
| 14 | 2 | `util/counting.v` ᶜ | 5 | 103 | `Util/Counting.lean` | ACCEPTED |
| 15 | 2 | `util/div_mod.v` ᶜ | 17 | 236 | `Util/DivMod.lean` | ACCEPTED |
| 16 | 2 | `util/fixedpoint.v` ᶜ | 10 | 190 | `Util/Fixedpoint.lean` | ACCEPTED |
| 17 | 2 | `util/sorting.v` ᶜ | 6 | 160 | `Util/Sorting.lean` | ACCEPTED |
| 18 | 2 | `util/step_function.v` ᶜ | 0 | 2 | `Util/StepFunction.lean` | ACCEPTED |
| 19 | 3 | `util/minmax.v` ᶜ | 44 | 543 | `Util/Minmax.lean` | ACCEPTED |
| 20 | 3 | `util/sum.v` ᶜ | 9 | 184 | `Util/Sum.lean` | ACCEPTED |
| 21 | 4 | `util/all.v` ᶜ | 0 | 20 | `Util/All.lean` | ACCEPTED |
| 22 | 5 | `util/find_seq.v` | 6 | 112 | `Util/FindSeq.lean` | ACCEPTED |
| 23 | 5 | `model/arrival/basic/task.v` ᶜ | 11 | 81 | `Model/Arrival/Basic/Task.lean` | ACCEPTED |
| 24 | 6 | `model/arrival/basic/arrival_sequence.v` ᶜ | 20 | 231 | `Model/Arrival/Basic/ArrivalSequence.lean` | ACCEPTED |
| 25 | 6 | `implementation/global/jitter/task.v` | 11 | 68 | `Implementation/Global/Jitter/Task.lean` | ACCEPTED |
| 26 | 6 | `implementation/task.v` | 10 | 67 | `Implementation/Task.lean` | ACCEPTED |
| 27 | 6 | `implementation/uni/jitter/task.v` | 11 | 68 | `Implementation/Uni/Jitter/Task.lean` | ACCEPTED |
| 28 | 6 | `implementation/uni/susp/dynamic/task.v` | 11 | 68 | `Implementation/Uni/Susp/Dynamic/Task.lean` | ACCEPTED |
| 29 | 7 | `model/arrival/basic/job.v` ᶜ | 8 | 93 | `Model/Arrival/Basic/Job.lean` | ACCEPTED |
| 30 | 7 | `model/arrival/jitter/arrival_sequence.v` | 15 | 222 | `Model/Arrival/Jitter/ArrivalSequence.lean` | ACCEPTED |
| 31 | 7 | `model/suspension.v` | 3 | 68 | `Model/Suspension.lean` | ACCEPTED |
| 32 | 7 | `implementation/global/jitter/job.v` | 11 | 64 | `Implementation/Global/Jitter/Job.lean` | ACCEPTED |
| 33 | 7 | `implementation/job.v` | 10 | 65 | `Implementation/Job.lean` | ACCEPTED |
| 34 | 7 | `implementation/uni/jitter/job.v` | 10 | 65 | `Implementation/Uni/Jitter/Job.lean` | ACCEPTED |
| 35 | 7 | `implementation/uni/susp/dynamic/job.v` | 10 | 65 | `Implementation/Uni/Susp/Dynamic/Job.lean` | ACCEPTED |
| 36 | 8 | `model/arrival/basic/task_arrival.v` ᶜ | 11 | 235 | `Model/Arrival/Basic/TaskArrival.lean` | ACCEPTED |
| 37 | 8 | `model/arrival/jitter/job.v` | 2 | 42 | `Model/Arrival/Jitter/Job.lean` | ACCEPTED |
| 38 | 8 | `model/policy_tdma.v` | 15 | 215 | `Model/PolicyTdma.lean` | ACCEPTED |
| 39 | 8 | `model/priority.v` ᶜ | 35 | 355 | `Model/Priority.lean` | ACCEPTED |
| 40 | 8 | `model/schedule/global/basic/schedule.v` ᶜ | 39 | 615 | `Model/Schedule/Global/Basic/Schedule.lean` | ACCEPTED |
| 41 | 8 | `model/schedule/global/jitter/job.v` | 2 | 39 | `Model/Schedule/Global/Jitter/Job.lean` | ACCEPTED |
| 42 | 8 | `model/schedule/uni/schedule.v` | 38 | 642 | `Model/Schedule/Uni/Schedule.lean` | ACCEPTED |
| 43 | 9 | `model/arrival/basic/arrival_bounds.v` ᶜ | 10 | 225 | `Model/Arrival/Basic/ArrivalBounds.lean` | ACCEPTED |
| 44 | 9 | `model/arrival/curves/bounds.v` | 7 | 90 | `Model/Arrival/Curves/Bounds.lean` | ACCEPTED |
| 45 | 9 | `model/arrival/jitter/task_arrival.v` | 8 | 198 | `Model/Arrival/Jitter/TaskArrival.lean` | ACCEPTED |
| 46 | 9 | `model/schedule/apa/affinity.v` ᶜ | 7 | 101 | `Model/Schedule/Apa/Affinity.lean` | ACCEPTED |
| 47 | 9 | `model/schedule/global/jitter/schedule.v` | 15 | 250 | `Model/Schedule/Global/Jitter/Schedule.lean` | ACCEPTED |
| 48 | 9 | `model/schedule/global/response_time.v` ᶜ | 5 | 134 | `Model/Schedule/Global/ResponseTime.lean` | ACCEPTED |
| 49 | 9 | `model/schedule/global/schedulability.v` ᶜ | 7 | 171 | `Model/Schedule/Global/Schedulability.lean` | ACCEPTED |
| 50 | 9 | `model/schedule/global/transformation/construction.v` | 6 | 150 | `Model/Schedule/Global/Transformation/Construction.lean` | ACCEPTED |
| 51 | 9 | `model/schedule/uni/basic/platform.v` | 5 | 187 | `Model/Schedule/Uni/Basic/Platform.lean` | ACCEPTED |
| 52 | 9 | `model/schedule/uni/basic/platform_tdma.v` | 3 | 66 | `Model/Schedule/Uni/Basic/PlatformTdma.lean` | ACCEPTED |
| 53 | 9 | `model/schedule/uni/jitter/schedule.v` | 9 | 168 | `Model/Schedule/Uni/Jitter/Schedule.lean` | ACCEPTED |
| 54 | 9 | `model/schedule/uni/limited/abstract_RTA/definitions.v` | 9 | 223 | `Model/Schedule/Uni/Limited/AbstractRTA/Definitions.lean` | ACCEPTED |
| 55 | 9 | `model/schedule/uni/limited/abstract_RTA/reduction_of_search_space.v` | 5 | 172 | `Model/Schedule/Uni/Limited/AbstractRTA/ReductionOfSearchSpace.lean` | ACCEPTED |
| 56 | 9 | `model/schedule/uni/nonpreemptive/schedule.v` | 11 | 354 | `Model/Schedule/Uni/Nonpreemptive/Schedule.lean` | ACCEPTED |
| 57 | 9 | `model/schedule/uni/response_time.v` | 6 | 166 | `Model/Schedule/Uni/ResponseTime.lean` | ACCEPTED |
| 58 | 9 | `model/schedule/uni/schedule_of_task.v` | 4 | 47 | `Model/Schedule/Uni/ScheduleOfTask.lean` | ACCEPTED |
| 59 | 9 | `model/schedule/uni/susp/last_execution.v` | 9 | 411 | `Model/Schedule/Uni/Susp/LastExecution.lean` | ACCEPTED |
| 60 | 9 | `model/schedule/uni/transformation/construction.v` | 7 | 169 | `Model/Schedule/Uni/Transformation/Construction.lean` | ACCEPTED |
| 61 | 9 | `model/schedule/uni/workload.v` | 6 | 135 | `Model/Schedule/Uni/Workload.lean` | ACCEPTED |
| 62 | 9 | `implementation/arrival_sequence.v` | 7 | 110 | `Implementation/ArrivalSequence.lean` | ACCEPTED |
| 63 | 9 | `implementation/global/jitter/arrival_sequence.v` | 7 | 109 | `Implementation/Global/Jitter/ArrivalSequence.lean` | ACCEPTED |
| 64 | 9 | `implementation/uni/jitter/arrival_sequence.v` | 8 | 116 | `Implementation/Uni/Jitter/ArrivalSequence.lean` | ACCEPTED |
| 65 | 9 | `implementation/uni/susp/dynamic/arrival_sequence.v` | 7 | 110 | `Implementation/Uni/Susp/Dynamic/ArrivalSequence.lean` | ACCEPTED |
| 66 | 10 | `model/arrival/jitter/arrival_bounds.v` | 10 | 249 | `Model/Arrival/Jitter/ArrivalBounds.lean` | ACCEPTED |
| 67 | 10 | `model/schedule/global/workload.v` ᶜ | 4 | 96 | `Model/Schedule/Global/Workload.lean` | ACCEPTED |
| 68 | 10 | `model/schedule/uni/end_time.v` | 21 | 308 | `Model/Schedule/Uni/EndTime.lean` | ACCEPTED |
| 69 | 10 | `model/schedule/uni/jitter/platform.v` | 4 | 98 | `Model/Schedule/Uni/Jitter/Platform.lean` | ACCEPTED |
| 70 | 10 | `model/schedule/uni/nonpreemptive/platform.v` | 6 | 120 | `Model/Schedule/Uni/Nonpreemptive/Platform.lean` | ACCEPTED |
| 71 | 10 | `model/schedule/uni/schedulability.v` | 4 | 122 | `Model/Schedule/Uni/Schedulability.lean` | ACCEPTED |
| 72 | 10 | `model/schedule/uni/service.v` | 18 | 585 | `Model/Schedule/Uni/Service.lean` | ACCEPTED |
| 73 | 10 | `model/schedule/uni/susp/suspension_intervals.v` | 12 | 521 | `Model/Schedule/Uni/Susp/SuspensionIntervals.lean` | ACCEPTED |
| 74 | 10 | `analysis/uni/basic/workload_bound_fp.v` | 6 | 246 | `Analysis/Uni/Basic/WorkloadBoundFp.lean` | ACCEPTED |
| 75 | 10 | `analysis/uni/susp/dynamic/jitter/jitter_schedule.v` | 6 | 161 | `Analysis/Uni/Susp/Dynamic/Jitter/JitterSchedule.lean` | ACCEPTED |
| 76 | 10 | `implementation/apa/task.v` | 11 | 73 | `Implementation/Apa/Task.lean` | ACCEPTED |
| 77 | 10 | `implementation/uni/basic/schedule.v` | 10 | 190 | `Implementation/Uni/Basic/Schedule.lean` | ACCEPTED |
| 78 | 11 | `model/schedule/apa/interference.v` ᶜ | 11 | 271 | `Model/Schedule/Apa/Interference.lean` | ACCEPTED |
| 79 | 11 | `model/schedule/global/basic/interference.v` ᶜ | 9 | 204 | `Model/Schedule/Global/Basic/Interference.lean` | ACCEPTED |
| 80 | 11 | `model/schedule/partitioned/schedule.v` | 5 | 128 | `Model/Schedule/Partitioned/Schedule.lean` | ACCEPTED |
| 81 | 11 | `model/schedule/uni/jitter/busy_interval.v` | 15 | 715 | `Model/Schedule/Uni/Jitter/BusyInterval.lean` | ACCEPTED |
| 82 | 11 | `model/schedule/uni/jitter/valid_schedule.v` | 1 | 65 | `Model/Schedule/Uni/Jitter/ValidSchedule.lean` | ACCEPTED |
| 83 | 11 | `model/schedule/uni/limited/platform/definitions.v` | 14 | 238 | `Model/Schedule/Uni/Limited/Platform/Definitions.lean` | ACCEPTED |
| 84 | 11 | `model/schedule/uni/limited/schedule.v` | 9 | 168 | `Model/Schedule/Uni/Limited/Schedule.lean` | ACCEPTED |
| 85 | 11 | `model/schedule/uni/susp/schedule.v` | 1 | 47 | `Model/Schedule/Uni/Susp/Schedule.lean` | ACCEPTED |
| 86 | 11 | `model/schedule/uni/sustainability.v` | 38 | 358 | `Model/Schedule/Uni/Sustainability.lean` | ACCEPTED |
| 87 | 11 | `analysis/apa/workload_bound.v` ᶜ | 21 | 743 | `Analysis/Apa/WorkloadBound.lean` | ACCEPTED |
| 88 | 11 | `analysis/global/basic/workload_bound.v` ᶜ | 21 | 742 | `Analysis/Global/Basic/WorkloadBound.lean` | ACCEPTED |
| 89 | 11 | `analysis/global/jitter/workload_bound.v` | 21 | 771 | `Analysis/Global/Jitter/WorkloadBound.lean` | ACCEPTED |
| 90 | 11 | `analysis/global/parallel/workload_bound.v` | 18 | 528 | `Analysis/Global/Parallel/WorkloadBound.lean` | ACCEPTED |
| 91 | 11 | `analysis/uni/arrival_curves/workload_bound.v` | 8 | 357 | `Analysis/Uni/ArrivalCurves/WorkloadBound.lean` | ACCEPTED |
| 92 | 11 | `analysis/uni/basic/tdma_wcrt_analysis.v` | 30 | 837 | `Analysis/Uni/Basic/TdmaWcrtAnalysis.lean` | ACCEPTED |
| 93 | 11 | `analysis/uni/jitter/workload_bound_fp.v` | 6 | 266 | `Analysis/Uni/Jitter/WorkloadBoundFp.lean` | ACCEPTED |
| 94 | 11 | `analysis/uni/susp/dynamic/jitter/jitter_taskset_generation.v` | 2 | 60 | `Analysis/Uni/Susp/Dynamic/Jitter/JitterTasksetGeneration.lean` | ACCEPTED |
| 95 | 11 | `implementation/apa/job.v` | 10 | 63 | `Implementation/Apa/Job.lean` | ACCEPTED |
| 96 | 11 | `implementation/uni/jitter/schedule.v` | 10 | 194 | `Implementation/Uni/Jitter/Schedule.lean` | ACCEPTED |
| 97 | 12 | `model/schedule/apa/platform.v` ᶜ | 5 | 115 | `Model/Schedule/Apa/Platform.lean` | ACCEPTED |
| 98 | 12 | `model/schedule/global/basic/platform.v` ᶜ | 6 | 188 | `Model/Schedule/Global/Basic/Platform.lean` | ACCEPTED |
| 99 | 12 | `model/schedule/global/jitter/interference.v` | 9 | 213 | `Model/Schedule/Global/Jitter/Interference.lean` | ACCEPTED |
| 100 | 12 | `model/schedule/partitioned/schedulability.v` | 2 | 131 | `Model/Schedule/Partitioned/Schedulability.lean` | ACCEPTED |
| 101 | 12 | `model/schedule/uni/limited/abstract_RTA/sufficient_condition_for_lock_in_service.v` | 4 | 262 | `Model/Schedule/Uni/Limited/AbstractRTA/SufficientConditionForLockInService.lean` | ACCEPTED |
| 102 | 12 | `model/schedule/uni/limited/busy_interval.v` | 33 | 1279 | `Model/Schedule/Uni/Limited/BusyInterval.lean` | ACCEPTED |
| 103 | 12 | `model/schedule/uni/limited/platform/limited.v` | 29 | 414 | `Model/Schedule/Uni/Limited/Platform/Limited.lean` | ACCEPTED |
| 104 | 12 | `model/schedule/uni/limited/platform/nonpreemptive.v` | 3 | 156 | `Model/Schedule/Uni/Limited/Platform/Nonpreemptive.lean` | ACCEPTED |
| 105 | 12 | `model/schedule/uni/limited/platform/preemptive.v` | 3 | 69 | `Model/Schedule/Uni/Limited/Platform/Preemptive.lean` | ACCEPTED |
| 106 | 12 | `model/schedule/uni/limited/rbf.v` | 3 | 104 | `Model/Schedule/Uni/Limited/Rbf.lean` | ACCEPTED |
| 107 | 12 | `model/schedule/uni/susp/build_suspension_table.v` | 4 | 263 | `Model/Schedule/Uni/Susp/BuildSuspensionTable.lean` | ACCEPTED |
| 108 | 12 | `model/schedule/uni/susp/platform.v` | 4 | 104 | `Model/Schedule/Uni/Susp/Platform.lean` | ACCEPTED |
| 109 | 12 | `analysis/apa/interference_bound.v` ᶜ | 1 | 44 | `Analysis/Apa/InterferenceBound.lean` | ACCEPTED |
| 110 | 12 | `analysis/global/basic/interference_bound.v` ᶜ | 1 | 42 | `Analysis/Global/Basic/InterferenceBound.lean` | ACCEPTED |
| 111 | 12 | `analysis/global/parallel/interference_bound.v` | 1 | 42 | `Analysis/Global/Parallel/InterferenceBound.lean` | ACCEPTED |
| 112 | 12 | `analysis/uni/basic/tdma_rta_theory.v` | 6 | 246 | `Analysis/Uni/Basic/TdmaRtaTheory.lean` | ACCEPTED |
| 113 | 12 | `analysis/uni/jitter/fp_rta_theory.v` | 1 | 133 | `Analysis/Uni/Jitter/FpRtaTheory.lean` | ACCEPTED |
| 114 | 12 | `analysis/uni/susp/sustainability/singlecost/reduction.v` | 4 | 101 | `Analysis/Uni/Susp/Sustainability/Singlecost/Reduction.lean` | ACCEPTED |
| 115 | 12 | `implementation/apa/arrival_sequence.v` | 7 | 112 | `Implementation/Apa/ArrivalSequence.lean` | ACCEPTED |
| 116 | 12 | `implementation/uni/basic/extraction_tdma.v` | 13 | 92 | `Implementation/Uni/Basic/ExtractionTdma.lean` | ACCEPTED |
| 117 | 13 | `model/schedule/apa/constrained_deadlines.v` ᶜ | 4 | 287 | `Model/Schedule/Apa/ConstrainedDeadlines.lean` | ACCEPTED |
| 118 | 13 | `model/schedule/apa/interference_edf.v` | 1 | 78 | `Model/Schedule/Apa/InterferenceEdf.lean` | ACCEPTED |
| 119 | 13 | `model/schedule/global/basic/constrained_deadlines.v` ᶜ | 6 | 442 | `Model/Schedule/Global/Basic/ConstrainedDeadlines.lean` | ACCEPTED |
| 120 | 13 | `model/schedule/global/basic/interference_edf.v` ᶜ | 1 | 71 | `Model/Schedule/Global/Basic/InterferenceEdf.lean` | ACCEPTED |
| 121 | 13 | `model/schedule/global/jitter/platform.v` | 6 | 195 | `Model/Schedule/Global/Jitter/Platform.lean` | ACCEPTED |
| 122 | 13 | `model/schedule/uni/limited/abstract_RTA/abstract_rta.v` | 8 | 457 | `Model/Schedule/Uni/Limited/AbstractRTA/AbstractRta.lean` | ACCEPTED |
| 123 | 13 | `model/schedule/uni/limited/platform/priority_inversion_is_bounded.v` | 9 | 592 | `Model/Schedule/Uni/Limited/Platform/PriorityInversionIsBounded.lean` | ACCEPTED |
| 124 | 13 | `model/schedule/uni/susp/valid_schedule.v` | 1 | 74 | `Model/Schedule/Uni/Susp/ValidSchedule.lean` | ACCEPTED |
| 125 | 13 | `analysis/apa/interference_bound_fp.v` ᶜ | 1 | 55 | `Analysis/Apa/InterferenceBoundFp.lean` | ACCEPTED |
| 126 | 13 | `analysis/global/basic/interference_bound_fp.v` ᶜ | 1 | 45 | `Analysis/Global/Basic/InterferenceBoundFp.lean` | ACCEPTED |
| 127 | 13 | `analysis/global/jitter/interference_bound.v` | 1 | 45 | `Analysis/Global/Jitter/InterferenceBound.lean` | ACCEPTED |
| 128 | 13 | `analysis/global/parallel/interference_bound_fp.v` | 1 | 44 | `Analysis/Global/Parallel/InterferenceBoundFp.lean` | ACCEPTED |
| 129 | 13 | `analysis/uni/basic/fp_rta_theory.v` | 1 | 140 | `Analysis/Uni/Basic/FpRtaTheory.lean` | ACCEPTED |
| 130 | 13 | `analysis/uni/jitter/fp_rta_comp.v` | 14 | 406 | `Analysis/Uni/Jitter/FpRtaComp.lean` | ACCEPTED |
| 131 | 13 | `analysis/uni/susp/dynamic/oblivious/reduction.v` | 29 | 741 | `Analysis/Uni/Susp/Dynamic/Oblivious/Reduction.lean` | ACCEPTED |
| 132 | 13 | `analysis/uni/susp/sustainability/allcosts/reduction.v` | 9 | 164 | `Analysis/Uni/Susp/Sustainability/Allcosts/Reduction.lean` | ACCEPTED |
| 133 | 13 | `analysis/uni/susp/sustainability/singlecost/reduction_properties.v` | 18 | 733 | `Analysis/Uni/Susp/Sustainability/Singlecost/ReductionProperties.lean` | ACCEPTED |
| 134 | 13 | `implementation/apa/schedule.v` | 24 | 664 | `Implementation/Apa/Schedule.lean` | ACCEPTED |
| 135 | 13 | `implementation/global/basic/schedule.v` | 14 | 263 | `Implementation/Global/Basic/Schedule.lean` | ACCEPTED |
| 136 | 13 | `implementation/uni/basic/schedule_tdma.v` | 11 | 251 | `Implementation/Uni/Basic/ScheduleTdma.lean` | ACCEPTED |
| 137 | 13 | `implementation/uni/susp/schedule.v` | 11 | 250 | `Implementation/Uni/Susp/Schedule.lean` | ACCEPTED |
| 138 | 14 | `model/schedule/global/jitter/constrained_deadlines.v` | 6 | 469 | `Model/Schedule/Global/Jitter/ConstrainedDeadlines.lean` | ACCEPTED |
| 139 | 14 | `model/schedule/global/jitter/interference_edf.v` | 1 | 75 | `Model/Schedule/Global/Jitter/InterferenceEdf.lean` | ACCEPTED |
| 140 | 14 | `model/schedule/uni/limited/abstract_RTA/abstract_seq_rta.v` | 11 | 641 | `Model/Schedule/Uni/Limited/AbstractRTA/AbstractSeqRta.lean` | ACCEPTED |
| 141 | 14 | `analysis/apa/bertogna_fp_theory.v` ᶜ | 13 | 1048 | `Analysis/Apa/BertognaFpTheory.lean` | ACCEPTED |
| 142 | 14 | `analysis/apa/interference_bound_edf.v` | 41 | 1204 | `Analysis/Apa/InterferenceBoundEdf.lean` | ACCEPTED |
| 143 | 14 | `analysis/global/basic/bertogna_fp_theory.v` ᶜ | 10 | 787 | `Analysis/Global/Basic/BertognaFpTheory.lean` | ACCEPTED |
| 144 | 14 | `analysis/global/basic/interference_bound_edf.v` ᶜ | 41 | 1199 | `Analysis/Global/Basic/InterferenceBoundEdf.lean` | ACCEPTED |
| 145 | 14 | `analysis/global/jitter/interference_bound_fp.v` | 1 | 45 | `Analysis/Global/Jitter/InterferenceBoundFp.lean` | ACCEPTED |
| 146 | 14 | `analysis/global/parallel/bertogna_fp_theory.v` | 6 | 468 | `Analysis/Global/Parallel/BertognaFpTheory.lean` | ACCEPTED |
| 147 | 14 | `analysis/global/parallel/interference_bound_edf.v` | 28 | 833 | `Analysis/Global/Parallel/InterferenceBoundEdf.lean` | ACCEPTED |
| 148 | 14 | `analysis/uni/basic/fp_rta_comp.v` | 13 | 393 | `Analysis/Uni/Basic/FpRtaComp.lean` | ACCEPTED |
| 149 | 14 | `analysis/uni/susp/dynamic/jitter/jitter_schedule_properties.v` | 9 | 457 | `Analysis/Uni/Susp/Dynamic/Jitter/JitterScheduleProperties.lean` | ACCEPTED |
| 150 | 14 | `analysis/uni/susp/dynamic/jitter/taskset_membership.v` | 8 | 349 | `Analysis/Uni/Susp/Dynamic/Jitter/TasksetMembership.lean` | ACCEPTED |
| 151 | 14 | `analysis/uni/susp/sustainability/allcosts/reduction_properties.v` | 22 | 933 | `Analysis/Uni/Susp/Sustainability/Allcosts/ReductionProperties.lean` | ACCEPTED |
| 152 | 14 | `implementation/global/jitter/schedule.v` | 14 | 269 | `Implementation/Global/Jitter/Schedule.lean` | ACCEPTED |
| 153 | 14 | `implementation/uni/basic/tdma_rta_example.v` | 14 | 197 | `Implementation/Uni/Basic/TdmaRtaExample.lean` | ACCEPTED |
| 154 | 14 | `implementation/uni/jitter/fp_rta_example.v` | 6 | 183 | `Implementation/Uni/Jitter/FpRtaExample.lean` | ACCEPTED |
| 155 | 15 | `model/schedule/uni/limited/jlfp_instantiation.v` | 12 | 773 | `Model/Schedule/Uni/Limited/JlfpInstantiation.lean` | ACCEPTED |
| 156 | 15 | `analysis/apa/bertogna_edf_theory.v` | 16 | 1018 | `Analysis/Apa/BertognaEdfTheory.lean` | ACCEPTED |
| 157 | 15 | `analysis/apa/bertogna_fp_comp.v` | 20 | 726 | `Analysis/Apa/BertognaFpComp.lean` | ACCEPTED |
| 158 | 15 | `analysis/global/basic/bertogna_edf_theory.v` ᶜ | 14 | 820 | `Analysis/Global/Basic/BertognaEdfTheory.lean` | ACCEPTED |
| 159 | 15 | `analysis/global/basic/bertogna_fp_comp.v` | 20 | 706 | `Analysis/Global/Basic/BertognaFpComp.lean` | ACCEPTED |
| 160 | 15 | `analysis/global/jitter/bertogna_fp_theory.v` | 10 | 829 | `Analysis/Global/Jitter/BertognaFpTheory.lean` | ACCEPTED |
| 161 | 15 | `analysis/global/jitter/interference_bound_edf.v` | 41 | 1305 | `Analysis/Global/Jitter/InterferenceBoundEdf.lean` | ACCEPTED |
| 162 | 15 | `analysis/global/parallel/bertogna_edf_theory.v` | 9 | 505 | `Analysis/Global/Parallel/BertognaEdfTheory.lean` | ACCEPTED |
| 163 | 15 | `analysis/global/parallel/bertogna_fp_comp.v` | 20 | 689 | `Analysis/Global/Parallel/BertognaFpComp.lean` | ACCEPTED |
| 164 | 15 | `analysis/uni/susp/dynamic/jitter/jitter_schedule_service.v` | 27 | 1260 | `Analysis/Uni/Susp/Dynamic/Jitter/JitterScheduleService.lean` | ACCEPTED |
| 165 | 15 | `analysis/uni/susp/dynamic/oblivious/fp_rta.v` | 1 | 160 | `Analysis/Uni/Susp/Dynamic/Oblivious/FpRta.lean` | ACCEPTED |
| 166 | 15 | `analysis/uni/susp/sustainability/allcosts/main_claim.v` | 1 | 164 | `Analysis/Uni/Susp/Sustainability/Allcosts/MainClaim.lean` | ACCEPTED |
| 167 | 15 | `implementation/uni/basic/fp_rta_example.v` | 6 | 162 | `Implementation/Uni/Basic/FpRtaExample.lean` | ACCEPTED |
| 168 | 16 | `model/schedule/uni/limited/edf/response_time_bound.v` | 9 | 653 | `Model/Schedule/Uni/Limited/Edf/ResponseTimeBound.lean` | ACCEPTED |
| 169 | 16 | `model/schedule/uni/limited/fixed_priority/response_time_bound.v` | 7 | 435 | `Model/Schedule/Uni/Limited/FixedPriority/ResponseTimeBound.lean` | ACCEPTED |
| 170 | 16 | `analysis/apa/bertogna_edf_comp.v` | 30 | 1002 | `Analysis/Apa/BertognaEdfComp.lean` | ACCEPTED |
| 171 | 16 | `analysis/global/basic/bertogna_edf_comp.v` | 30 | 990 | `Analysis/Global/Basic/BertognaEdfComp.lean` | ACCEPTED |
| 172 | 16 | `analysis/global/jitter/bertogna_edf_theory.v` | 14 | 871 | `Analysis/Global/Jitter/BertognaEdfTheory.lean` | ACCEPTED |
| 173 | 16 | `analysis/global/jitter/bertogna_fp_comp.v` | 20 | 726 | `Analysis/Global/Jitter/BertognaFpComp.lean` | ACCEPTED |
| 174 | 16 | `analysis/global/parallel/bertogna_edf_comp.v` | 30 | 985 | `Analysis/Global/Parallel/BertognaEdfComp.lean` | ACCEPTED |
| 175 | 16 | `analysis/uni/susp/dynamic/jitter/rta_by_reduction.v` | 2 | 201 | `Analysis/Uni/Susp/Dynamic/Jitter/RtaByReduction.lean` | ACCEPTED |
| 176 | 16 | `implementation/apa/bertogna_fp_example.v` | 15 | 295 | `Implementation/Apa/BertognaFpExample.lean` | ACCEPTED |
| 177 | 16 | `implementation/global/basic/bertogna_fp_example.v` | 7 | 176 | `Implementation/Global/Basic/BertognaFpExample.lean` | ACCEPTED |
| 178 | 16 | `implementation/global/parallel/bertogna_fp_example.v` | 7 | 195 | `Implementation/Global/Parallel/BertognaFpExample.lean` | ACCEPTED |
| 179 | 16 | `implementation/uni/susp/dynamic/oblivious/fp_rta_example.v` | 6 | 186 | `Implementation/Uni/Susp/Dynamic/Oblivious/FpRtaExample.lean` | ACCEPTED |
| 180 | 17 | `model/schedule/uni/limited/edf/nonpr_reg/response_time_bound.v` | 4 | 345 | `Model/Schedule/Uni/Limited/Edf/NonprReg/ResponseTimeBound.lean` | ACCEPTED |
| 181 | 17 | `model/schedule/uni/limited/fixed_priority/nonpr_reg/response_time_bound.v` | 4 | 291 | `Model/Schedule/Uni/Limited/FixedPriority/NonprReg/ResponseTimeBound.lean` | ACCEPTED |
| 182 | 17 | `analysis/global/jitter/bertogna_edf_comp.v` | 30 | 1084 | `Analysis/Global/Jitter/BertognaEdfComp.lean` | ACCEPTED |
| 183 | 17 | `analysis/uni/susp/dynamic/jitter/taskset_rta.v` | 2 | 232 | `Analysis/Uni/Susp/Dynamic/Jitter/TasksetRta.lean` | ACCEPTED |
| 184 | 17 | `implementation/apa/bertogna_edf_example.v` | 13 | 210 | `Implementation/Apa/BertognaEdfExample.lean` | ACCEPTED |
| 185 | 17 | `implementation/global/basic/bertogna_edf_example.v` | 5 | 134 | `Implementation/Global/Basic/BertognaEdfExample.lean` | ACCEPTED |
| 186 | 17 | `implementation/global/jitter/bertogna_fp_example.v` | 7 | 180 | `Implementation/Global/Jitter/BertognaFpExample.lean` | ACCEPTED |
| 187 | 17 | `implementation/global/parallel/bertogna_edf_example.v` | 5 | 138 | `Implementation/Global/Parallel/BertognaEdfExample.lean` | ACCEPTED |
| 188 | 18 | `model/schedule/uni/limited/edf/nonpr_reg/concrete_models/response_time_bound.v` | 5 | 634 | `Model/Schedule/Uni/Limited/Edf/NonprReg/ConcreteModels/ResponseTimeBound.lean` | ACCEPTED |
| 189 | 18 | `model/schedule/uni/limited/fixed_priority/nonpr_reg/concrete_models/response_time_bound.v` | 4 | 608 | `Model/Schedule/Uni/Limited/FixedPriority/NonprReg/ConcreteModels/ResponseTimeBound.lean` | ACCEPTED |
| 190 | 18 | `implementation/global/jitter/bertogna_edf_example.v` | 5 | 139 | `Implementation/Global/Jitter/BertognaEdfExample.lean` | ACCEPTED |
<!-- TABLE_END -->
