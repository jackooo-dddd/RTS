# Report: `classic/model/arrival/basic/arrival_sequence.v` (rank 23)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/arrival/basic/arrival_sequence.v` |
| sha256 | `0cc7bf24b6a29b5fe266e579e5e48e1c30db7a12eab5bdc171e8caadc118aedb` |
| Lean module | `Prosa/Classic/Model/Arrival/Basic/ArrivalSequence.lean` (namespace `Prosa.Classic.Model.Arrival.Basic.ArrivalSequence`) |
| Tier / layer | S / 7 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (20 source → Lean, same names)

- `Definition` `ArrivalSequence.arrival_sequence`
- `Definition` `ArrivalSequence.jobs_arriving_at`
- `Definition` `ArrivalSequence.arrives_at`
- `Definition` `ArrivalSequence.arrives_in`
- `Definition` `ArrivalSequence.arrival_times_are_consistent`
- `Definition` `ArrivalSequence.arrival_sequence_is_a_set`
- `Definition` `ArrivalSequence.has_arrived`
- `Definition` `ArrivalSequence.arrived_before`
- `Definition` `ArrivalSequence.arrived_between`
- `Definition` `ArrivalSequence.jobs_arrived_between`
- `Definition` `ArrivalSequence.jobs_arrived_up_to`
- `Definition` `ArrivalSequence.jobs_arrived_before`
- `Lemma` `ArrivalSequence.job_arrived_between_cat`
- `Lemma` `ArrivalSequence.jobs_arrived_between_mem_cat`
- `Lemma` `ArrivalSequence.jobs_arrived_between_sub`
- `Lemma` `ArrivalSequence.in_arrivals_implies_arrived`
- `Lemma` `ArrivalSequence.in_arrivals_implies_arrived_between`
- `Lemma` `ArrivalSequence.in_arrivals_implies_arrived_before`
- `Lemma` `ArrivalSequence.arrived_between_implies_in_arrivals`
- `Lemma` `ArrivalSequence.arrivals_uniq`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `bigCat_split`.

## Representation notes

Job arrival sequences (Rocq module `ArrivalSequence`, which `Export`s `Time`).

Representation notes:
* `arrival_sequence Job := time → seq Job` is `time → List Job`.
* `j \in s` returning `bool` is `decide (j ∈ s)`; inside propositions it is
  `j ∈ s`; Boolean range tests `t1 <= x < t2` are
  `decide (t1 ≤ x) && decide (x < t2)`.
* `\cat_(t1 <= t < t2) F t` is the accepted v0.6 helper
  `Prosa.Util.Notation.bigCat t1 t2 F` (as in the v0.6 `arrivals_between`).
* Binder lists follow the Rocq contract: e.g. `in_arrivals_implies_arrived` does
  not take the consistency hypothesis (its proof term does not use it), while
  the other prefix lemmas take `job_arrival arr_seq H_arrival_times_are_consistent`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
