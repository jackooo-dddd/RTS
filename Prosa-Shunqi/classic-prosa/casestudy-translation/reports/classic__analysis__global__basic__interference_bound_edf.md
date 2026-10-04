# Report: `classic/analysis/global/basic/interference_bound_edf.v` (rank 48)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/analysis/global/basic/interference_bound_edf.v` |
| sha256 | `baffd3b8f1ffdff6ba878f5dee757fdbd38cef123778e8c72d724921f2765cb1` |
| Lean module | `Prosa/Classic/Analysis/Global/Basic/InterferenceBoundEdf.lean` (namespace `Prosa.Classic.Analysis.Global.Basic.InterferenceBoundEdf`) |
| Tier / layer | P / 15 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (41 source → Lean, same names)

- `Definition` `InterferenceBoundEDF.edf_specific_interference_bound`
- `Definition` `InterferenceBoundEDF.interference_bound_edf`
- `Definition` `InterferenceBoundEDF.total_interference_bound_edf`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_use_another_definition`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_simpl_by_filtering_interfering_jobs`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_simpl_by_sorting_interfering_jobs`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_job_in_same_sequence`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_all_jobs_from_tsk_k`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_jobs_ordered_by_arrival`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_interference_le_task_cost`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_holds_for_at_most_n_k_jobs`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_at_least_one_job`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_j_fst_is_job_of_tsk_k`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_j_fst_deadline`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_j_i_deadline`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_j_fst_completion_implies_rt_bound_inside_interval`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_simpl_when_there's_one_job`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_holds_for_single_job_that_completes_on_time`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_response_time_bound_of_j_fst_after_interval`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_holds_for_single_job_with_big_slack`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_holds_for_single_job_with_small_slack`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_interference_of_j_fst_limited_by_slack`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_holds_for_a_single_job`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_j_lst_is_job_of_tsk_k`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_j_lst_deadline`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_j_fst_before_j_lst`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_last_job_arrives_before_end_of_interval`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_j_fst_completed_on_time`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_many_periods_in_between`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_n_k_covers_middle_jobs_plus_one`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_holds_for_middle_and_last_jobs`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_n_k_equals_num_mid_jobs_plus_one`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_remainder_ge_slack`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_simpl_by_moving_to_left_side`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_interference_of_j_fst_bounded_by_response_time`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_bounding_interference_with_interval_lengths`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_simpl_by_concatenation_of_intervals`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_interference_of_j_fst_limited_by_remainder_and_slack`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_holds_for_multiple_jobs`
- `Theorem` `InterferenceBoundEDF.interference_bound_edf_bounds_interference`
- `Lemma` `InterferenceBoundEDF.interference_bound_edf_monotonic`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `getD_lt`, `sumSeq_getD`, `sum_filter_ne_zero`, `sorted_mem`, `sorted_nodup`, `job_interference_le_length`, `job_interference_le_until_completion`, `interfering_job_arrives_before`, `sorted_job_deadline_le`.

## Representation notes

Bertogna and Cirinei's EDF-specific interference bound and its safety proof (Rocq
module `InterferenceBoundEDF`).

Representation notes:
* The `let d_tsk := … in …` of `edf_specific_interference_bound` is inlined;
  `minn` is `min`, `m %% d` is `m % d` and `m %/ d` is `m / d`.
* `\sum_((tsk_other, R_other) <- R_prev | other_task tsk_other) F` binds the pair by
  pattern matching and is `Prosa.Util.Sum.sumFiltered R_prev
  (fun (tsk_other, _R_other) => different_task tsk tsk_other)
  (fun (tsk_other, R_other) => F)`.
* The section-local `Let`s are unfolded in the statements: `x` is
  `task_interference job_arrival job_cost job_task sched j_i tsk_k (job_arrival j_i)
  (job_arrival j_i + delta)`, `interference_bound` is
  `edf_specific_interference_bound task_cost task_period task_deadline tsk_i tsk_k R_k`,
  `t1`/`t2` are `job_arrival j_i` / `job_arrival j_i + delta`, `D_i`, `D_k`, `p_k`
  are `task_deadline tsk_i`, `task_deadline tsk_k`, `task_period tsk_k`, `n_k` is
  `div_floor D_i p_k`, `interference_caused_by j' t1 t2` is
  `job_interference job_arrival job_cost sched j_i j' t1 t2`, `interfering_jobs` is
  the filter of `jobs_scheduled_between sched t1 t2` by
  `decide (job_task j' = tsk_k) && !decide (interference_caused_by j' t1 t2 = 0)`,
  `sorted_jobs` is its `mergeSort` by arrival time (MathComp's stable `sort`), and
  `j_fst` / `j_lst` / `a_fst` / `a_lst` are `sorted_jobs.getD 0 elem`,
  `sorted_jobs.getD (num_mid_jobs + 1) elem` and their arrival times.
* `\sum_(j <- s) F j` is `Prosa.Util.Sum.sumSeq s F`, `\sum_(j <- s | P j) F j` is
  `Prosa.Util.Sum.sumFiltered s P F`, `\sum_(a <= t < b) F t` is
  `∑ t ∈ Finset.Ico a b, F t`; `x != 0` in proposition position is
  `(!decide (x = 0)) = true` and `j \in s` as a Boolean equation is `decide (j ∈ s)`.
* The Rocq module re-exports `InterferenceBoundGeneric`.
* Binder lists follow the Rocq contract (`About` on the Rocq 9.3 reference build),
  including which section hypotheses (e.g. `H_many_jobs`, `H_only_one_job`) each
  lemma abstracts; some binders are unused by the Lean proofs.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
