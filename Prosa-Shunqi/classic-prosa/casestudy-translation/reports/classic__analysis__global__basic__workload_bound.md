# Report: `classic/analysis/global/basic/workload_bound.v` (rank 36)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/analysis/global/basic/workload_bound.v` |
| sha256 | `2dac207ab4344b0840108fd9b23a21172d7d63dda1d1bc7b908d029951858022` |
| Lean module | `Prosa/Classic/Analysis/Global/Basic/WorkloadBound.lean` (namespace `Prosa.Classic.Analysis.Global.Basic.WorkloadBound`) |
| Tier / layer | P / 12 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (21 source → Lean, same names)

- `Definition` `WorkloadBound.max_jobs`
- `Definition` `WorkloadBound.W`
- `Lemma` `WorkloadBound.W_monotonic`
- `Lemma` `WorkloadBound.workload_bound_simpl_by_sorting_scheduled_jobs`
- `Lemma` `WorkloadBound.workload_bound_job_in_same_sequence`
- `Lemma` `WorkloadBound.workload_bound_all_jobs_from_tsk`
- `Lemma` `WorkloadBound.workload_bound_jobs_ordered_by_arrival`
- `Lemma` `WorkloadBound.workload_bound_holds_for_at_most_n_k_jobs`
- `Lemma` `WorkloadBound.workload_bound_j_fst_is_job_of_tsk`
- `Lemma` `WorkloadBound.workload_bound_holds_for_a_single_job`
- `Lemma` `WorkloadBound.workload_bound_j_lst_is_job_of_tsk`
- `Lemma` `WorkloadBound.workload_bound_response_time_of_first_job_inside_interval`
- `Lemma` `WorkloadBound.workload_bound_last_job_arrives_before_end_of_interval`
- `Lemma` `WorkloadBound.workload_bound_service_of_first_and_last_jobs`
- `Lemma` `WorkloadBound.workload_bound_simpl_expression_with_first_and_last`
- `Lemma` `WorkloadBound.workload_bound_service_of_middle_jobs`
- `Lemma` `WorkloadBound.workload_bound_many_periods_in_between`
- `Lemma` `WorkloadBound.workload_bound_n_k_covers_middle_jobs`
- `Lemma` `WorkloadBound.workload_bound_n_k_equals_num_mid_jobs`
- `Lemma` `WorkloadBound.workload_bound_n_k_equals_num_mid_jobs_plus_1`
- `Theorem` `WorkloadBound.workload_bounded_by_W`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `W_eq`, `W_core_monotone`, `getD_lt`, `sorted_mem`, `sorted_nodup`, `sorted_pairwise`, `sumSeq_getD`, `service_le_length`, `first_le_last`.

## Representation notes

Bertogna and Cirinei's workload bound (Rocq module `WorkloadBound`, classic/analysis/global/basic/workload_bound.v).

Representation notes:
* The section-local `Let`s are unfolded in the statements: `sorted_jobs` is
  `(jobs_of_task_scheduled_between job_task sched tsk t1 (t1 + delta)).mergeSort
  (fun x y => decide (job_arrival x ≤ job_arrival y))` (MathComp's stable `sort`),
  `t2` is `t1 + delta`, `n_k` is `max_jobs task_cost task_period tsk R_tsk delta`,
  `workload_bound` is `W task_cost task_period tsk R_tsk delta`, `workload_of` is
  `workload job_task sched`, `job_has_completed_by` is `completed job_cost sched`,
  and `j_fst` / `j_lst` are `sorted_jobs.getD 0 elem` /
  `sorted_jobs.getD (num_mid_jobs + 1) elem`.
* The `let e_k := … in let p_k := … in` of `W` is inlined; `minn` is `min`.
* `\sum_(i <- s) F i` is `Prosa.Util.Sum.sumSeq s F`; `\sum_(a <= i < b)` is
  `∑ i ∈ Finset.Ico a b`; `x != 0` in proposition position is
  `(!decide (x = 0)) = true`; `j \in s` as a Boolean equation is `decide (j ∈ s)`.
* Binder lists follow the Rocq contract (`About` on the Rocq 9.3 reference build).

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
