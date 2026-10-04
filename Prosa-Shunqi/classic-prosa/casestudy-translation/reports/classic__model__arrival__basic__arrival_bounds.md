# Report: `classic/model/arrival/basic/arrival_bounds.v` (rank 28)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/arrival/basic/arrival_bounds.v` |
| sha256 | `a4ef38c8fabfcc1d0dc518afe758be88342f5f8dc16218ff546aec8b079f9a93` |
| Lean module | `Prosa/Classic/Model/Arrival/Basic/ArrivalBounds.lean` (namespace `Prosa.Classic.Model.Arrival.Basic.ArrivalBounds`) |
| Tier / layer | S / 10 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (10 source → Lean, same names)

- `Lemma` `ArrivalBounds.sporadic_arrival_bound_no_jobs`
- `Lemma` `ArrivalBounds.sporadic_arrival_bound_more_than_one_point`
- `Lemma` `ArrivalBounds.sporadic_arrival_bound_one_job`
- `Corollary` `ArrivalBounds.sporadic_arrival_bound_properties_of_nth`
- `Corollary` `ArrivalBounds.sporadic_arrival_bound_distance_between_first_and_last`
- `Lemma` `ArrivalBounds.sporadic_arrival_bound_last_job_too_far`
- `Lemma` `ArrivalBounds.sporadic_arrival_bound_last_arrives_too_late`
- `Lemma` `ArrivalBounds.sporadic_arrival_bound_case_3_contradiction`
- `Lemma` `ArrivalBounds.sporadic_task_arrival_bound_at_least_two_jobs`
- `Theorem` `ArrivalBounds.sporadic_task_arrival_bound`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `le_div_ceil_mul`.

## Representation notes

Upper bound on the number of arrivals of a sporadic task (Rocq module
`ArrivalBounds`).

Representation notes: as in `TaskArrival` (section-local `Let`s unfolded,
`sort` is `List.mergeSort`, `nth` is `getD`, Boolean chains are
`(decide … && decide …) = true`).  `div_ceil` is the classic
`prosa.classic.util.div_mod.div_ceil` (checked with `Set Printing Fully
Qualified` on the Rocq reference build).  Binder lists follow the Rocq contract:
each lemma takes exactly the section hypotheses its Rocq proof uses.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
