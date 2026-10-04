# Report: `classic/analysis/global/basic/bertogna_fp_theory.v` (rank 47)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/analysis/global/basic/bertogna_fp_theory.v` |
| sha256 | `521399cd2702714377a3d5ad672acfd0d5afba34cff975845fba9cbc75972c17` |
| Lean module | `Prosa/Classic/Analysis/Global/Basic/BertognaFpTheory.lean` (namespace `Prosa.Classic.Analysis.Global.Basic.BertognaFpTheory`) |
| Tier / layer | P / 15 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (10 source → Lean, same names)

- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_workload_bounds_interference`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_too_much_interference`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_interference_by_different_tasks`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_all_cpus_are_busy`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_interference_on_all_cpus`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_interference_in_non_full_processors`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_minimum_exceeds_interference`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_sum_exceeds_total_interference`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_exists_task_that_exceeds_bound`
- `Theorem` `ResponseTimeAnalysisFP.bertogna_cirinei_response_time_bound_fp`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `countP_eq_sum_toNat`, `sum_min_split`, `interference_in_non_full_processors_core`, `hp_jobs_complete_by_period`, `tsk_jobs_complete_by_period`.

## Representation notes

Bertogna and Cirinei's response-time analysis for global FP scheduling (Rocq module
`ResponseTimeAnalysisFP`): any fixed point of the recurrence is a safe response-time
bound (Baruah et al., *Multiprocessor Scheduling for Real-time Systems*, Ch. 18.2).

Representation notes:
* The section-local `Let`s are unfolded in the statements: `x tsk_other` is
  `task_interference job_arrival job_cost job_task sched j tsk_other (job_arrival j)
  (job_arrival j + R)`, `X` is `total_interference job_arrival job_cost sched j
  (job_arrival j) (job_arrival j + R)`, `workload_bound tsk_other R_other` is
  `W task_cost task_period tsk_other R_other R`, `is_hp_task` is
  `higher_priority_task higher_eq_priority tsk`, `hp_tasks` is
  `ts.val.filter (fun tsk_other => higher_priority_task higher_eq_priority tsk tsk_other)`,
  `other_scheduled_task t` is `fun tsk_other => task_is_scheduled job_task sched
  tsk_other t && higher_priority_task higher_eq_priority tsk tsk_other`,
  `num_tasks_exceeding delta` is `hp_tasks.countP (fun i => decide (delta ≤ x i))`
  and `response_time_bounded_by` is `is_response_time_bound_of_task … sched`.
* `count P s` is `s.countP P`; `\sum_(i <- s) F i` is `Prosa.Util.Sum.sumSeq s F`,
  `\sum_(i <- s | P i) F i` is `Prosa.Util.Sum.sumFiltered s P F`, and
  `\sum_((tsk_k, R_k) <- s) F` binds the pair by pattern matching; `minn` is `min`;
  Boolean chains `a <= b < c` in proposition position are
  `(decide (a ≤ b) && decide (b < c)) = true`; `x != y` in proposition position is
  `(!decide (x = y)) = true`.
* The Rocq module `Export`s the classic model modules it uses; Lean clients open
  those namespaces directly.
* Binder lists follow the Rocq contract (`About` on the Rocq 9.3 reference build),
  including which section hypotheses each lemma abstracts.  Rocq abstracts every
  section hypothesis its proof script mentions, so some binders are unused here.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
