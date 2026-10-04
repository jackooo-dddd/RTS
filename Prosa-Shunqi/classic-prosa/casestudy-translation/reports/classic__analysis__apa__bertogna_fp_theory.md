# Report: `classic/analysis/apa/bertogna_fp_theory.v` (rank 46)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/analysis/apa/bertogna_fp_theory.v` |
| sha256 | `bb00af339638096a6223ef7a0661f773090d6852bdaab3336b7fb5d8c432e199` |
| Lean module | `Prosa/Classic/Analysis/Apa/BertognaFpTheory.lean` (namespace `Prosa.Classic.Analysis.Apa.BertognaFpTheory`) |
| Tier / layer | P / 15 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (13 source → Lean, same names)

- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_workload_bounds_interference`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_too_much_interference`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_interference_by_different_tasks`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_previous_interfering_jobs_complete_by_their_period`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_all_cpus_in_affinity_busy`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_all_cpus_in_subaffinity_busy`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_alpha'_is_full`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_interference_in_non_full_processors`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_minimum_exceeds_interference`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_interference_on_subaffinity`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_sum_exceeds_total_interference`
- `Lemma` `ResponseTimeAnalysisFP.bertogna_fp_exists_task_that_exceeds_bound`
- `Theorem` `ResponseTimeAnalysisFP.bertogna_cirinei_response_time_bound_fp`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `countP_eq_sum_toNat`, `sum_min_split`, `interference_in_non_full_processors_core`, `running_job_is_hp`, `hp_task_in_of_cpu`.

## Representation notes

The APA reduction of Bertogna and Cirinei's response-time analysis for global FP
scheduling with processor affinities (Rocq module `ResponseTimeAnalysisFP`,
`classic/analysis/apa`): any fixed point of the recurrence computed with a
subaffinity `alpha'` is a safe response-time bound (Lemma 9 of the revised APA
paper, ECRTS 2013).

Representation notes:
* The section-local `Let`s are unfolded in the statements: `x tsk_other` is
  `task_interference job_arrival job_cost job_task sched alpha j tsk_other
  (job_arrival j) (job_arrival j + R)`, `X` is `total_interference job_arrival
  job_cost sched j (job_arrival j) (job_arrival j + R)`, `workload_bound tsk_other
  R_other` is `W task_cost task_period tsk_other R_other R`, `hp_task_in a` is
  `higher_priority_task_in alpha higher_eq_priority tsk a`, `hp_tasks_in a'` is
  `ts.val.filter (fun tsk_other => higher_priority_task_in alpha higher_eq_priority
  tsk (a' tsk) tsk_other)`, `scheduled_on_alpha_tsk t tsk_k` is
  `task_scheduled_on_affinity job_task sched (alpha tsk) tsk_k t`,
  `num_tasks_exceeding delta` is
  `(hp_tasks_in alpha').countP (fun i => decide (delta ≤ x i))` and
  `response_time_bounded_by` is `is_response_time_bound_of_task … sched`.
* `#|alpha' tsk|` is `(Finset.univ.filter (fun x => x ∈ alpha' tsk)).card` (as in
  `Affinity`); `count P s` is `s.countP P`; `\sum_(i <- s) F i` is
  `Prosa.Util.Sum.sumSeq s F` and `\sum_(i <- s | P i) F i` is
  `Prosa.Util.Sum.sumFiltered s P F`, with pairs bound by pattern matching; `minn`
  is `min`; Boolean chains `a <= b < c` in proposition position are
  `(decide (a ≤ b) && decide (b < c)) = true`; `x != y` in proposition position is
  `(!decide (x = y)) = true`.
* The Rocq module `Export`s the classic model modules it uses; Lean clients open
  those namespaces directly.
* Binder lists follow the Rocq contract (`About` on the Rocq 9.3 reference build),
  including which section hypotheses each lemma abstracts; Rocq abstracts every
  section hypothesis its proof script mentions, so some binders are unused here
  (e.g. `bertogna_fp_workload_bounds_interference` does not take
  `H_tsk_other_has_higher_priority`, which its proof does not use).

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
