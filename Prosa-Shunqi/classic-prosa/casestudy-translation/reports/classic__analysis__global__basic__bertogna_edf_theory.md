# Report: `classic/analysis/global/basic/bertogna_edf_theory.v` (rank 49)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/analysis/global/basic/bertogna_edf_theory.v` |
| sha256 | `642f7eb8726a649816a5f3a8c94801731e6d78e842c12947294af7e1c4ff4e3c` |
| Lean module | `Prosa/Classic/Analysis/Global/Basic/BertognaEdfTheory.lean` (namespace `Prosa.Classic.Analysis.Global.Basic.BertognaEdfTheory`) |
| Tier / layer | P / 16 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (14 source → Lean, same names)

- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_tsk_other_in_ts`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_R_other_ge_cost`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_workload_bounds_interference`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_specific_bound_holds`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_too_much_interference`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_interference_by_different_tasks`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_all_previous_jobs_complete_by_their_period`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_all_cpus_are_busy`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_interference_on_all_cpus`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_interference_in_non_full_processors`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_minimum_exceeds_interference`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_sum_exceeds_total_interference`
- `Lemma` `ResponseTimeAnalysisEDF.bertogna_edf_exists_task_that_exceeds_bound`
- `Theorem` `ResponseTimeAnalysisEDF.bertogna_cirinei_response_time_bound_edf`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `countP_eq_sum_toNat`, `sum_min_split`, `interference_in_non_full_processors_core`, `mem_ts_iff_bound`.

## Representation notes

Bertogna and Cirinei's response-time analysis for global EDF scheduling (Rocq module
`ResponseTimeAnalysisEDF`): any fixed point of the recurrence is a safe response-time
bound (Baruah et al., *Multiprocessor Scheduling for Real-time Systems*, Ch. 17.1.2).

Representation notes:
* The section-local `Let`s are unfolded in the statements: `I tsk delta` is
  `total_interference_bound_edf task_cost task_period task_deadline tsk rt_bounds delta`,
  `x tsk_other` is `task_interference job_arrival job_cost job_task sched j tsk_other
  (job_arrival j) (job_arrival j + R)`, `X` is `total_interference job_arrival job_cost
  sched j (job_arrival j) (job_arrival j + R)`, `workload_bound`, `edf_specific_bound` and
  `interference_bound` are `W …`, `edf_specific_interference_bound … tsk …` and
  `interference_bound_edf … tsk R (tsk_other, R_other)`, `other_task` is
  `different_task tsk`, `other_tasks` is `ts.val.filter (fun tsk_other => different_task
  tsk tsk_other)`, `other_scheduled_task t` is `fun tsk_other => task_is_scheduled job_task
  sched tsk_other t && different_task tsk tsk_other`, `num_tasks_exceeding delta` is
  `other_tasks.countP (fun i => decide (delta ≤ x i))` and `response_time_bounded_by` is
  `is_response_time_bound_of_task … sched`.
* `unzip1 rt_bounds = ts` is `rt_bounds.map Prod.fst = ts.val`; `count P s` is `s.countP P`;
  `\sum_(i <- s) F i` is `Prosa.Util.Sum.sumSeq s F`, `\sum_(i <- s | P i) F i` is
  `Prosa.Util.Sum.sumFiltered s P F`, and `\sum_((tsk_other, R_other) <- s | P) F` binds the
  pair by pattern matching; `minn` is `min`; Boolean chains `a <= b < c` in proposition
  position are `(decide (a ≤ b) && decide (b < c)) = true`; `x != y` in proposition position
  is `(!decide (x = y)) = true`.
* The Rocq module `Export`s the classic model modules it uses; Lean clients open those
  namespaces directly.
* Binder lists follow the Rocq contract (`About` on the Rocq 9.3 reference build), including
  which section hypotheses each lemma abstracts.  Rocq abstracts every section hypothesis its
  proof script mentions, so some binders are unused here.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
