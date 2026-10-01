# results/rta/ideal/edf/floating_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-10-06 15:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ideal/edf/floating_nonpreemptive.v`; layer 28; no dependents.
- Public declaration: **1** theorem, `uniprocessor_response_time_bound_edf_with_floating_nonpreemptive_regions`.
- Dependencies (all accepted):
  - `analysis/definitions/blocking_bound/edf.v`, `analysis/facts/preemption/rtc_threshold/floating.v`;
  - `analysis/facts/readiness/sequential.v`, `model/priority/edf.v`, `model/readiness/basic.v`;
  - `results/rta/ideal/edf/bounded_nps.v`.

## Translation

`Prosa/Results/Rta/Ideal/Edf/FloatingNonpreemptive.lean`; it compiles with only the standard Lean axioms.

- **Binders:** follow the elaborated type.
- **Section-local instances:** the basic readiness, the EDF policy (over `job_deadline_from_task_deadline`) and the
  accepted `limited_preemptive_job_model` are passed explicitly.
- **Search space and bounds:** `bounded_nps.is_in_search_space` is the accepted ideal EDF `bounded_nps` definition,
  `edf.blocking_bound` the accepted EDF blocking bound and `edf_athep_bound.bound_on_athep_workload` the accepted athep
  bound.

The proof follows the source. It applies the accepted ideal EDF `bounded_nps` theorem with:
- the limited-preemptive job model and the floating run-to-completion threshold;
- the accepted floating-nonpreemptive model facts (the model with bounded nonpreemptive regions, and the threshold's
  validity);
- the recurrence, which carries over since the floating threshold equals the task cost.

## Source binding

Extract mode, module `RtaIdealEdfFloatingNonpreemptiveSemanticSource`. The statement is the authoritative elaborated
type; its fingerprint is `STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`.

Bindings:
- **Base closure (the accepted ideal EDF `bounded_nps` run):** the accepted extracted `bounded_nps`, `bounded_pi`,
  blocking-bound, athep, limited-preemptive and task floating-nonpreemptive sources.
- **Validation-only module paths:** `Module bounded_nps := <the accepted ideal EDF bounded_nps source>.`,
  `Module edf_athep_bound := <the accepted athep source>.` and `Module edf := <the accepted EDF blocking-bound
  source>.`, recorded in the spec.
- **Printer repairs:** they make the basic readiness and the limited-preemptive job model explicit in
  `valid_schedule`, `work_conserving`, `respects_JLFP_policy_at_preemption_point` and
  `schedule_respects_preemption_model`, as in the accepted EDF files.

## Validation

- **Spec** `results_rta_ideal_edf_floating_nonpreemptive.json`; base run `results_rta_ideal_edf_bounded_nps`.
- **Export root:** the base root plus the statement.
- **Export:** 154,864 lines.

Certificate chain (56 modules):
- **The accepted ideal replay chain**, with the replayed `PreemptionTimeCorrespondence`, `EdfAthepBoundCorrespondence`,
  `LimitedPreemptiveCorrespondence`, `ScheduleLimitedPreemptiveCorrespondence` and
  `TaskFloatingNonpreemptiveCorrespondence`, and `IdlStateRel`.
  - `TaskFloatingNonpreemptiveCorrespondence` drops one block, `tfn_floating_preemptive_rtc_threshold_related`: it
    does not typecheck at this instance and is not used. Its header records the drop.
  - No other block was dropped.
- **`RtaIdealEdfFloatingNonpreemptiveCorrespondence.v`:**
  - **Helper part:** the accepted ideal helper part, without the helpers naming the ideal interference instances (not
    in this export; not used). The header records the drop.
  - **As in the accepted ideal EDF `bounded_nps` certificate:** the task-set predicates, the EDF policy, basic
    readiness, the policy at preemption points, the `bounded_pi` / `bounded_nps` search-space definitions, the
    conditional maximum and `blocking_relevant`.
  - **The limited-preemptive job model:** its relation, and covers for the in-statement job preemption points and
    task maximum nonpreemptive segments. The covers come from the accepted two-way class totals.
  - **The correspondence:** over the accepted RBF, blocking-bound, athep-bound, validity, work-conservation,
    preemption-model and response-time-bound relations.

No source or target theorem is used.

Attempts: prepare attempt 1 passed; finalization 1 was accepted.

Audit: 22 certificates, 17 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 5 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **334 / 357 files**, **2123 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
