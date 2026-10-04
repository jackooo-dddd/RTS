# Report: `classic/model/arrival/basic/task_arrival.v` (rank 25)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/arrival/basic/task_arrival.v` |
| sha256 | `76c1a80d3d80a97eee79c6be856bf78d644214ddb88a6b08976c4f69dea817db` |
| Lean module | `Prosa/Classic/Model/Arrival/Basic/TaskArrival.lean` (namespace `Prosa.Classic.Model.Arrival.Basic.TaskArrival`) |
| Tier / layer | S / 9 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (11 source → Lean, same names)

- `Definition` `TaskArrival.sporadic_task_model`
- `Definition` `TaskArrival.is_job_of_task`
- `Definition` `TaskArrival.arrivals_of_task_between`
- `Definition` `TaskArrival.arrivals_of_task_before`
- `Definition` `TaskArrival.num_arrivals_of_task`
- `Lemma` `TaskArrival.num_arrivals_of_task_cat`
- `Remark` `TaskArrival.sorted_arrivals_properties_of_nth`
- `Lemma` `TaskArrival.sorted_arrivals_current_differs_from_next`
- `Lemma` `TaskArrival.sorted_arrivals_separated_by_period`
- `Lemma` `TaskArrival.sorted_arrivals_distance_from_first_job`
- `Corollary` `TaskArrival.sorted_arrivals_distance_between_first_and_last`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `sortedJobs`, `sortedJobs_length`, `sortedJobs_mem`, `sortedJobs_pairwise`, `getD_lt`, `sortedJobs_nodup`.

## Representation notes

Properties of job arrivals of tasks (Rocq module `TaskArrival`).

Representation notes:
* Binder lists follow the Rocq contract (`About` on the Rocq 9.3 reference
  build), including which section hypotheses each lemma takes.
* The section-local `Let`s (`arrivals_between`, `arriving_jobs`, `num_arrivals`,
  `by_arrival_time`, `sorted_jobs`, `nth_job`, `j_first`, …) are unfolded in the
  statements, as Rocq does when the sections are closed.
* MathComp's `sort by_arrival_time s` (a stable merge sort) is
  `s.mergeSort (fun j j' => decide (job_arrival j ≤ job_arrival j'))`, which is
  also stable; for this total preorder both produce the same list.
* `job_task j == tsk` is `decide (job_task j = tsk)`; `[seq j <- s | P j]` is
  `s.filter P`; `nth elem s i` is `s.getD i elem`; `x.-1` is `x - 1`; a Boolean
  chain `a <= b < c` in proposition position is
  `(decide (a ≤ b) && decide (b < c)) = true`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
