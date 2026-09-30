# results/rta/ideal/fp/fully_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-10-06 08:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ideal/fp/fully_nonpreemptive.v`; layer 27; no dependents.
- Public declaration: **1** theorem, `uniprocessor_response_time_bound_fully_nonpreemptive_fp`.
- Dependencies (all accepted):
  - `analysis/facts/preemption/{rtc_threshold,task}/nonpreemptive.v`, `analysis/facts/readiness/sequential.v`;
  - `model/task/preemption/fully_nonpreemptive.v`, `results/rta/ideal/fp/bounded_nps.v`.

## Translation

`Prosa/Results/Rta/Ideal/Fp/FullyNonpreemptive.lean`; `#print axioms` shows only the standard axioms.

- **Binders:** follow the elaborated type.
- **Section-local instances:** the accepted `fully_nonpreemptive_job_model` and `sequential_ready_instance arr_seq`
  are passed explicitly.
- **Blocking bound:** the section-local `\max_(tsk_other <- ts | ~~ hep_task tsk_other tsk) (task_cost tsk_other - ε)`
  is the accepted `bigMaxListCond`. It is definitionally the accepted FP blocking bound at the fully nonpreemptive
  task model.

The proof follows the source:
- a zero-cost task makes every job complete immediately;
- otherwise the accepted ideal FP `bounded_nps` theorem applies, with:
  - the fully nonpreemptive job, task and run-to-completion models;
  - the accepted sequential-readiness facts;
  - the accepted fully nonpreemptive model facts (the valid preemption model from the nonpreemptive schedule on the
    ideal unit-service processor).

## Source binding

Extract mode, module `RtaIdealFpFullyNonpreemptiveSemanticSource`. The statement's fingerprint is
`STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`.

Bindings:
- **Base closure (the accepted ideal FP `fully_preemptive` run):** it already carries the pinned
  `model/readiness/sequential`, its patch and the `model/preemption/parameter` shim.
- **Pinned sources:** `model/preemption/fully_nonpreemptive` and `model/schedule/nonpreemptive`.
- **The fully nonpreemptive task model:** the accepted extracted `.vo`, hash-checked against its manifest.

The printer repairs make the section-local readiness and job model explicit, as in the accepted restricted-supply
file.

## Validation

- **Spec** `results_rta_ideal_fp_fully_nonpreemptive.json`; base run `results_rta_ideal_fp_fully_preemptive`.
- **Export:** 154,147 lines.

Certificate chain (52 modules):
- the accepted ideal replay chain (with the replayed `PreemptionTimeCorrespondence`), regenerated at this export with
  no block dropped;
- `RtaIdealFpFullyNonpreemptiveCorrespondence.v`:
  - **Helper part:** the accepted ideal helper part, without the unused interference-instance helpers.
  - **Carried over from the accepted ideal FP certificates:** the FP layer, sequential readiness, the policy at
    preemption points and the `bounded_pi` search space.
  - **The fully nonpreemptive job model:** as in the accepted restricted-supply certificate, via the accepted
    Boolean/eqb relations.
  - **`nonpreemptive_schedule`:** as in the accepted restricted-supply certificate.
  - **The section-local blocking bound:** the conditional-maximum relation over the exported `bigMaxListCond`
    equations.
  - **The correspondence.**

No source or target theorem is used.

Attempts:
- **Prepare attempt 1** was archived as `_attempt1_shim_exists`. The spec re-declared the
  `model/preemption/parameter` shim that the base run already provides, and the pipeline refused to overwrite it.
- **Prepare attempt 2** passed with the shim removed.
- **Finalization 1** was accepted.

Audit: 17 certificates, 14 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 3 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **327 / 357 files**, **2105 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
