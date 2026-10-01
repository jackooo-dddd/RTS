# results/rta/ideal/fp/limited_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-06 10:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ideal/fp/limited_preemptive.v`; layer 27; no dependents.
- Public declaration: **1** theorem, `uniprocessor_response_time_bound_fp_with_fixed_preemption_points`.
- Dependencies (all accepted):
  - `analysis/definitions/blocking_bound/fp.v`, `analysis/facts/preemption/rtc_threshold/limited.v`;
  - `analysis/facts/readiness/sequential.v`, `model/task/preemption/limited_preemptive.v`;
  - `results/rta/ideal/fp/bounded_nps.v`.

## Translation

`Prosa/Results/Rta/Ideal/Fp/LimitedPreemptive.lean`; `#print axioms` shows only the standard axioms.

- **Binders:** follow the elaborated type. The job and task preemption points are in-statement class binders.
- **Section-local instances:** the accepted `limited_preemptive_job_model` and `sequential_ready_instance arr_seq`
  are passed explicitly.
- **Blocking bound:** taken at the task model induced by the task preemption points (the accepted conversion
  instance).

The proof follows the source:
- a zero-cost task makes every job complete immediately;
- otherwise the accepted ideal FP `bounded_nps` theorem applies, with:
  - the limited-preemptions run-to-completion threshold;
  - the accepted `fixed_preemption_points_model_is_valid_model_with_bounded_nonpreemptive_regions` and
    `limited_valid_task_run_to_completion_threshold`;
  - `last_segment_eq_cost_minus_rtct`, which rewrites the cost-minus-threshold terms;
  - the accepted sequential-readiness facts.

## Source binding

Extract mode, module `RtaIdealFpLimitedPreemptiveSemanticSource`. The statement's fingerprint is
`STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`.

Bindings:
- **Base closure:** the accepted ideal FP `floating_nonpreemptive` run. It carries the limited-preemptive and
  schedule-limited-preemptive extracted sources, and `NondecreasingInterface.nthD` in its export root.
- **The task limited-preemptive extracted source:** the accepted `.vo`, hash-checked against its manifest.
- **Printer repairs:** as in the accepted floating file.

## Validation

- **Spec** `results_rta_ideal_fp_limited_preemptive.json`; base run `results_rta_ideal_fp_floating_nonpreemptive`.
- **Export:** 154,750 lines.

Certificate chain (55 modules):
- **The accepted ideal replay chain**, with the replayed `PreemptionTimeCorrespondence`.
- **The replayed accepted restricted-supply limited certificates:**
  - `LimitedPreemptiveCorrespondence`, with no block dropped;
  - `ScheduleLimitedPreemptiveCorrespondence`, with no block dropped;
  - `TaskLimitedPreemptiveCorrespondence`, with one unused block dropped: `tlp_limited_preemptions_rtc_threshold_related`,
    which relates a source-local helper of the restricted-supply file.
- **`IdlStateRel`.**
- **`RtaIdealFpLimitedPreemptiveCorrespondence.v`:**
  - **Helper part:** the accepted ideal helper part, without the unused interference-instance helpers.
  - **As in the accepted floating certificate:** the FP layer, sequential readiness, the policy at preemption points,
    the `bounded_pi` search space, the job-preemption-points cover and the limited job model.
  - **The task-preemption-points cover:** from the accepted two-way totals of `TppPointsRel`.
  - **The blocking bound:** at the converted segment model, via the accepted conversion correspondence.
  - **`task_last_nonpr_segment`:** the accepted certificate.
  - **`valid_fixed_preemption_points_model`:** the replayed accepted certificate.

No source or target theorem is used.

Attempts:
- **Prepare attempt 1** passed.
- **Finalization 1** stopped at the replayed helper aliases `IdlTaskLimitedPreemptiveCorrespondence.I.{True,HEq,HEq_inst1}`.
  They were added via `allowalias.py`; the log is archived.
- **Finalization 2** was accepted.

Audit: 19 certificates, 16 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 3 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **329 / 357 files**, **2107 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
