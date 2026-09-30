# results/rta/ideal/fp/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-06 07:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ideal/fp/fully_preemptive.v`; layer 27; 1 dependent.
- Public declaration: **1** theorem, `uniprocessor_response_time_bound_fully_preemptive_fp`.
- Dependencies (all accepted):
  - `analysis/facts/preemption/{rtc_threshold,task}/preemptive.v`, `analysis/facts/readiness/sequential.v`;
  - `model/task/preemption/fully_preemptive.v`, `results/rta/ideal/fp/bounded_nps.v`.

## Translation

`Prosa/Results/Rta/Ideal/Fp/FullyPreemptive.lean`; `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound`.

- **Binders:** follow the elaborated type.
- **Section-local instances:** the accepted `fully_preemptive_job_model` and `sequential_ready_instance arr_seq`
  (the local `sequential_readiness`) are passed explicitly.
- **Search space:** `fp.bounded_pi.is_in_search_space` is the accepted ideal FP `bounded_pi` definition.

The proof follows the source. It applies the accepted ideal FP `bounded_nps` theorem with:
- the fully preemptive job, task and run-to-completion models;
- the accepted sequential-readiness facts (work-bearing readiness, sequential tasks);
- the accepted fully preemptive model facts;
- the FP blocking bound, which vanishes in the fully preemptive task model (proved as in the accepted
  restricted-supply file).

## Source binding

Extract mode, module `RtaIdealFpFullyPreemptiveSemanticSource`. The statement is the authoritative elaborated type;
its fingerprint is `STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`.

Bindings:
- **Base closure (the accepted ideal FP `bounded_nps` run):** the accepted `bounded_nps` / `bounded_pi` extracted
  sources.
- **`model/readiness/sequential` and `model/preemption/fully_preemptive`:** the pinned sources.
  - `model/readiness/sequential` is under its accepted Rocq 9.3 compatibility patch.
  - `model/preemption/parameter` is shimmed to the accepted extracted source, as in the accepted restricted-supply
    file.
- **The fully preemptive task model:** the accepted extracted `.vo`, hash-checked against its manifest.
- **The `fp.bounded_pi` module alias:** as in the accepted `bounded_nps` file.

Recorded printer repairs make the section-local readiness and job model explicit in `valid_schedule`,
`work_conserving` and `respects_FP_policy_at_preemption_point`, as in the accepted restricted-supply file.

## Validation

- **Spec** `results_rta_ideal_fp_fully_preemptive.json`; base run `results_rta_ideal_fp_bounded_nps`.
- **Export root:** the base root plus the statement.
- **Export:** 154,032 lines.

Certificate chain (52 modules):
- the accepted ideal replay chain, with the replayed `PreemptionTimeCorrespondence` and `IdlStateRel`, regenerated at
  this export with no block dropped;
- `RtaIdealFpFullyPreemptiveCorrespondence.v`:
  - **Helper part:** the accepted ideal `iw_instantiation` helper part, without the helpers naming the ideal
    interference instances (not in this export; not used). The header records the drop.
  - **Local helpers:** the FP policy layer, task-set predicates, the FP policy at preemption points and the
    `bounded_pi` search-space definition certificate, all as in the accepted ideal FP `bounded_nps` certificate.
  - **Section-local models:** the sequential readiness at the related schedule pair (pending plus the accepted
    `prior_jobs_complete` relation) and the fully preemptive job model. Both are as in the accepted
    restricted-supply FP fully-preemptive certificate.
  - **The correspondence:** over the accepted RBF, validity, work-conservation and response-time-bound relations.

No source or target theorem is used.

Attempts: prepare attempt 1 passed; finalization 1 was accepted.

Audit: 14 certificates, 11 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 3 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **326 / 357 files**, **2104 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
