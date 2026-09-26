# analysis/facts/periodic/arrival_separation.v — canonical translation report

First experiment timestamp: **2026-09-30 07:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/periodic/arrival_separation.v`; rank 192.
- Public declarations: **3**: `consecutive_job_separation`, `job_arrival_separation_when_index_diff_is_k`, `job_sep_periodic`.
- Dependencies `analysis/facts/sporadic/arrival_times.v` and `model/task/arrival/periodic_as_sporadic.v`: accepted.

## Translation

`Prosa/Analysis/Facts/Periodic/ArrivalSeparation.lean`. Binders follow the elaborated types.

Conventions:
- A Boolean in `Prop` position is `= true`.
- `n > 0` is `0 < n`.
- The sporadic facts are used through the accepted `periodic_as_sporadic` instance, as in the source.

Proofs:
- `consecutive_job_separation`: the periodic predecessor of `j2` has the index of `j1`, so it is `j1` (accepted `equal_index_implies_equal_jobs`).
- The index-difference lemma is by induction on `k`, generalising `j1`:
  - the step picks the job with index `job_index j1 + 1` (accepted `exists_jobs_before_j`);
  - it uses the consecutive case;
  - it orders the arrivals with the accepted `lower_index_implies_earlier_arrival`.
- `job_sep_periodic`: distinct jobs with ordered arrivals have strictly ordered indices; this reduces to the index-difference lemma.

Lean axioms: none beyond the standard ones.

## Source binding

The statements are extracted from the authoritative elaborated types (module `FactsPeriodicArrivalSeparationSemanticSource`).
- The `periodic_as_sporadic` import is bound to its accepted extracted source (`PeriodicAsSporadicSemanticSource` with `PeriodicSemanticSource`), hash-checked as base.
- `model/task/arrivals` is the compiled pinned source of the base run.
- The proof-only `facts/sporadic/arrival_times` import is dropped.

All 3 statements match the evidence (fingerprint: 3 checked, 0 mismatches).

## Validation

Spec `analysis_facts_periodic_arrival_separation.json`; base run `model_task_arrival_periodic_as_sporadic_final`.

Artifacts: the accepted sporadic `ArrivalTimes` `.olean` is copied and hash-checked.

Export: 30,220 lines. The root is the accepted periodic-as-sporadic export root without its statements (task-arrival / arrival-sequence interfaces), plus the three statements.

Attempts: none failed. The assumption audit passed on the first finalize.

Certificate chain:
- The accepted ArrivalsSeq*/Arrivals/Periodic certificates, re-bound.
- The new `FactsPeriodicArrivalSeparationCorrespondence.v`:
  - Statements are specialised at the leading inputs: the periodic model (accepted `PerRel`), `job_task` by `Lean.eq`, `job_arrival` by `ArJobArrivalRel`, and the arrival sequence by `ArArrivalSequenceRel`.
  - Tasks and jobs are identity carriers. The Nats `k` and `n` are covered in both directions.
  - Four notions are closed by the accepted certificates: arrival-sequence validity, `respects_periodic_task_model`, `valid_period`, and `job_index` (via `job_index_correspondence`).
  - No source or target theorem is used.

Audit: 5 certificates (3 principal, 2 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`.

## Formal acceptance

Coverage **182 / 357 files**, **1298 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
