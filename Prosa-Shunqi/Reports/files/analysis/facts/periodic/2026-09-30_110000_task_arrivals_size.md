# analysis/facts/periodic/task_arrivals_size.v — canonical translation report

First experiment timestamp: **2026-09-30 11:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/periodic/task_arrivals_size.v`; rank 196.
- Public declarations: **8**:
  - general: `task_arrivals_size_at_non_arrival`, `task_arrivals_at_size_cases`, `size_task_arrivals_between_eq0`;
  - under `infinite_jobs`: `jobs_exists_later`, `task_arrivals_at_size`, `size_task_arrivals_up_to_offset`, `task_arrivals_up_to_size`, `eq_size_of_task_arrivals_seperated_by_period`.
- Dependencies `analysis/definitions/infinite_jobs.v`, `analysis/facts/periodic/arrival_times.v` and `analysis/facts/sporadic/arrival_sequence.v`: accepted.

## Translation

`Prosa/Analysis/Facts/Periodic/TaskArrivalsSize.lean`. Binders follow the elaborated types; for example, `task_arrivals_at_size_cases` has no task-offset instance.

Conventions:
- `size s` is `s.length`; `[::]` is `[]`; `x.+1` is `x + 1`, as in the accepted sporadic arrival-sequence file.
- The statement-level `let`s are kept, including the unused `r` of `task_arrivals_up_to_size`, which gives a linter warning only.
- The sporadic facts are used through the accepted `periodic_as_sporadic` instance, as in the source.

Proofs:
- Arrival times: the accepted periodic `job_arrival_times` and `periodic_arrival_times`.
- At most one arrival at an instant: sporadic separation, where a duplicate would contradict a positive period.
- Singleton lists: the accepted `only_j_in_task_arrivals_at_j`.
- Interval decompositions: the accepted `task_arrivals_between_cat`, `task_arrivals_cat` and `size_of_task_arrivals_between`, with a local zero-sum lemma.
- Periodicity of sizes: case split on `(t - offset) mod period`.

Lean axioms: none beyond the standard ones.

## Source binding

The statements are extracted from the authoritative elaborated types (module `FactsPeriodicTaskArrivalsSizeSemanticSource`).
- The task-offset and periodic models are bound to their accepted extracted sources, hash-checked in the base.
- `analysis/definitions/infinite_jobs` is compiled from the pinned tree, as in its accepted run.
- The proof-only `facts/periodic/arrival_times` and `facts/sporadic/arrival_sequence` imports are dropped. The task-arrival lists come from the pinned `model/task/arrivals`.

All 8 statements match the evidence (fingerprint: 8 checked, 0 mismatches).

## Validation

Spec `analysis_facts_periodic_task_arrivals_size.json`; base run `analysis_facts_periodic_arrival_times_final`.

Artifacts: the following accepted `.olean` files are copied and hash-checked:
- `InfiniteJobs`;
- `Sporadic`;
- `PeriodicAsSporadic`;
- sporadic `ArrivalTimes`;
- sporadic `ArrivalSequence`.

Export: 136,571 lines. The export root:
- is the accepted periodic arrival-times export root without its statements;
- is merged with the accepted infinite-jobs root;
- adds the eight statements.

Attempts: no archived failures.
- A certificate argument-order slip was fixed before the first finalize.
- The assumption audit first flagged the two `InfiniteJobsCorrespondence.I.*` alias names as unexpected. They are the same SProp aliases as for the other re-bound chains; they were added to the alias allow-list and pruned where unobserved.

Certificate chain:
- The accepted offset-family ArrivalsSeq*/Arrivals/JitterSvc*/PreemptionParameter/TaskOffset certificates, re-bound.
- The accepted `PeriodicCorrespondence` and `InfiniteJobsCorrespondence`, re-bound.
- The new `FactsPeriodicTaskArrivalsSizeCorrespondence.v`:
  - Statements are specialised at the leading inputs: the accepted `OffRel` where it occurs, `PerRel`, `job_task` by `Lean.eq`, `ArJobArrivalRel`, and the arrival sequence.
  - Tasks and jobs are identity carriers; Nats are covered in both directions.
  - The task-arrival lists are related by the accepted arrivals certificates, their sizes by `ari_size_related`, and `x.+1` by `ari_succ_related`.
  - `= [::]` is related through the list conversion's round trip.
  - No source or target theorem is used.

Audit: 8 certificates (8 principal). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`.

## Formal acceptance

Coverage **186 / 357 files**, **1314 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
