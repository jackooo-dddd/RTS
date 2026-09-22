# behavior/arrival_sequence.v — canonical translation report

First experiment timestamp: **2026-09-22 22:29:29 +08:00**  
Latest progress update: **2026-09-22 22:36:51 +08:00**

## Current status

Rank 23 is dependency-ready: `behavior/job.v` and `util/notation.v` are both
`ACCEPTED_V06_FILE`. The authoritative file has 14 declarations. Translation
and semantic validation are in progress; none of these declarations is yet
counted as accepted.

## Initial representation audit

- `arrival_sequence` is an instant-indexed ordered sequence, hence Lean
  `instant → List Job`; order and multiplicity remain observable.
- The source `arrives_at`, `has_arrived`, `arrived_before`, and
  `arrived_between` are MathComp Boolean computations. The historical Lean
  candidate rendered several of them as `Prop`; the v0.6 translation must keep
  their result as `Bool` under the approved policy.
- `arrives_in`, consistency, uniqueness, and validity are propositions whose
  Boolean subexpressions are reflected explicitly.
- `arrivals_between` uses the already accepted half-open ordered `bigCat`
  representation, not a `Finset`; `arrivals_between_P` is the new-in-v0.6
  filtered-list declaration missing from the historical candidate.
- Every source `JobType` boundary retains explicit Lean `DecidableEq`
  evidence.

## Planned correspondence reuse

The target should compose existing certified relations for Job equality,
instant/Nat order, ordered seq/List, membership, Nodup, Bool truth, List
filter, and half-open big concatenation. Only an artifact-local adapter for the
new compiled module should be needed; no new global representation decision is
planned.

Evidence starts at
`Validation/planning/v06_pipeline/behavior_arrival_sequence_selection.json`.
This report will be updated in place; no second report will be created for the
same source file.

## 2026-09-22 22:36:51 +08:00 — complete Lean candidate written and compiled

All 14 authoritative public declarations now have production candidates in
`Prosa/Behavior/Arrival_sequence.lean`, in source order:

```text
arrival_sequence
arrivals_at
arrives_at
arrives_in
consistent_arrival_times
arrival_sequence_uniq
valid_arrival_sequence
has_arrived
arrived_before
arrived_between
arrivals_between
arrivals_up_to
arrivals_before
arrivals_between_P
```

The whole candidate file passes an isolated Lean 4.33.1 compile. The produced
preflight `.olean` has SHA-256
`49a0cd72dd999b09adee6f0eaadddde549565c65da522c2f8a688a7ef98baeab`;
the current Lean source has SHA-256
`0fdb7632034b9b5fd3cd88ce739dffad38be4e8c4a3cafd8df718cb762092355`.
This is compile evidence only, not semantic acceptance.

The translation audit found a material reason not to copy the historical Lean
file blindly: the official v0.6 declarations `arrives_at`, `has_arrived`,
`arrived_before`, and `arrived_between` elaborate to `bool`. The new candidate
therefore preserves Boolean computation, while proposition-valued declarations
such as `arrives_in`, consistency, uniqueness, and validity remain `Prop`.
`arrivals_between_P`, which has no historical candidate, is translated as an
ordered, multiplicity-preserving list filter over the certified half-open
`bigCat` representation.

Current declaration state:

| Dimension | Result |
|---|---:|
| authoritative declarations mapped | 14 / 14 |
| Lean candidates written | 14 / 14 |
| isolated Lean compile | PASS |
| semantic certificates accepted | 0 / 14 |
| file acceptance | `IN_PROGRESS` |

The next gate is the actual compiled-type/body audit followed by one frozen
export/import preparation and compositional Rocq certificates. Until those
gates and the fail-closed assumption audit pass, cumulative accepted coverage
remains 22 files and 209 declarations.
