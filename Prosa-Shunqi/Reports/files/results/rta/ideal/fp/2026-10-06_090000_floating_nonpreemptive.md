# results/rta/ideal/fp/floating_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-10-06 09:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ideal/fp/floating_nonpreemptive.v`; layer 27; no dependents.
- Public declaration: **1** theorem, `uniprocessor_response_time_bound_fp_with_floating_nonpreemptive_regions`.
- Dependencies (all accepted):
  - `analysis/definitions/blocking_bound/fp.v`, `analysis/facts/preemption/rtc_threshold/floating.v`;
  - `analysis/facts/readiness/sequential.v`, `results/rta/ideal/fp/bounded_nps.v`.

## Translation

`Prosa/Results/Rta/Ideal/Fp/FloatingNonpreemptive.lean`; `#print axioms` shows only the standard axioms.

- **Binders:** follow the elaborated type. The job preemption points and the maximal nonpreemptive segments are
  in-statement class binders.
- **Section-local instances:** the accepted `limited_preemptive_job_model` and `sequential_ready_instance arr_seq`
  are passed explicitly.

The proof follows the source. It applies the accepted ideal FP `bounded_nps` theorem with:
- the floating run-to-completion threshold (equal to the cost, so the cost-minus-threshold terms vanish);
- the accepted floating-model fact
  `floating_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions`;
- the accepted sequential-readiness facts.

## Source binding

Extract mode, module `RtaIdealFpFloatingNonpreemptiveSemanticSource`. The statement's fingerprint is
`STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`.

Bindings:
- **Base closure:** the accepted ideal FP `fully_nonpreemptive` run.
- **Copied `.vo` files** (from their accepted runs, hash-checked against their manifests): the task
  floating-nonpreemptive, limited-preemptive and schedule-limited-preemptive extracted sources.
- **Printer repairs:** make the section-local readiness and job model explicit in `valid_schedule`,
  `work_conserving`, `schedule_respects_preemption_model` and `respects_FP_policy_at_preemption_point`, as in the
  accepted restricted-supply file.

## Validation

- **Spec** `results_rta_ideal_fp_floating_nonpreemptive.json`; base run `results_rta_ideal_fp_fully_nonpreemptive`.
- **Export root:** the base root, plus the accepted fixture definition `NondecreasingInterface.nthD` (see Attempts),
  plus the statement.
- **Export:** 154,433 lines.

Certificate chain (55 modules):
- **The accepted ideal replay chain**, with the replayed `PreemptionTimeCorrespondence`.
- **The accepted restricted-supply FP floating certificates**, replayed at the ideal instance of this export:
  - `LimitedPreemptiveCorrespondence`, with no block dropped;
  - `ScheduleLimitedPreemptiveCorrespondence`, with no block dropped;
  - `TaskFloatingNonpreemptiveCorrespondence`, with one unused block dropped: `tfn_floating_preemptive_rtc_threshold_related`,
    which relates a source-local helper of the restricted-supply file.
- **`IdlStateRel`.**
- **`RtaIdealFpFloatingNonpreemptiveCorrespondence.v`:**
  - **Helper part:** the accepted ideal helper part, without the unused interference-instance helpers.
  - **Carried over from the accepted ideal FP certificates:** the FP layer, sequential readiness, the policy at
    preemption points and the `bounded_pi` search space.
  - **Covers for the in-statement job preemption points and maximal nonpreemptive segments:** from the accepted
    two-way totals of `LpJobPreemptionPointsRel` / `TppMaxSegmentRel`.
  - **The limited-preemptive job model:** the accepted `lp_limited_preemptive_job_model_related`.
  - **The FP blocking bound at the covered segment model:** over the exported `bigMaxListCond` equations.
  - **The correspondence:** the floating-model validity and schedule-respects-model relations are the replayed
    accepted certificates.

No source or target theorem is used.

Attempts:
- **Prepare attempt 1** passed but was archived as `_attempt1_missing_nthD`. The replayed
  `LimitedPreemptiveCorrespondence` needs the fixture definition `NondecreasingInterface.nthD`, which the ideal export
  roots did not contain. Without it, the replay dropped its preemption-point helpers and, with them, the floating
  validity correspondence.
- **Prepare attempt 2** added that single definition to the export root, as in the accepted restricted-supply
  export root.
- **Finalization 1** stopped at the replayed helper aliases `Idl{LimitedPreemptive,ScheduleLimitedPreemptive,TaskFloatingNonpreemptive}Correspondence.I.{True,HEq,HEq_inst1}`.
  They were added via `allowalias.py`; the log is archived.
- **Finalization 2** was accepted.

Audit: 19 certificates, 16 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 3 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **328 / 357 files**, **2106 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
