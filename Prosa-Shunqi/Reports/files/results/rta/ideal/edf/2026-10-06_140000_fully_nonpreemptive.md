# results/rta/ideal/edf/fully_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-10-06 14:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ideal/edf/fully_nonpreemptive.v`; layer 28; no dependents.
- Public declaration: **1** theorem, `uniprocessor_response_time_bound_fully_nonpreemptive_edf`.
- Dependencies (all accepted):
  - `analysis/facts/preemption/{rtc_threshold,task}/nonpreemptive.v`, `analysis/facts/readiness/basic.v`;
  - `model/priority/edf.v`, `model/readiness/basic.v`, `model/task/preemption/fully_nonpreemptive.v`;
  - `results/rta/ideal/edf/bounded_nps.v`.

## Translation

`Prosa/Results/Rta/Ideal/Edf/FullyNonpreemptive.lean`; it compiles with only the standard Lean axioms.

- **Binders:** follow the elaborated type.
- **Section-local instances:** the basic readiness, the EDF policy (over `job_deadline_from_task_deadline`) and the
  accepted `fully_nonpreemptive_job_model` are passed explicitly.
- **The blocking bound:** at the fully nonpreemptive task model it is the accepted `bigMaxListCond`, as in the
  elaborated statement.
- **Search space and bounds:** `bounded_nps.is_in_search_space` is the accepted ideal EDF `bounded_nps` definition, and
  `edf_athep_bound.bound_on_athep_workload` is the accepted athep bound.

The proof follows the source:
- **Zero-cost task:** a task with zero cost has only zero-cost jobs, which complete immediately.
- **Otherwise:** it applies the accepted ideal EDF `bounded_nps` theorem with the fully nonpreemptive job, task and
  run-to-completion models and the accepted fully nonpreemptive model facts. The run-to-completion validity uses the
  positive task cost.

## Source binding

Extract mode, module `RtaIdealEdfFullyNonpreemptiveSemanticSource`. The statement is the authoritative elaborated type;
its fingerprint is `STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`.

Bindings:
- **Base closure (the accepted ideal EDF `bounded_nps` run):** the accepted extracted `bounded_nps`, `bounded_pi`,
  blocking-bound and athep sources, and the accepted fully nonpreemptive task model source.
- **Validation-only module paths:** `Module bounded_nps := <the accepted ideal EDF bounded_nps source>.` and
  `Module edf_athep_bound := <the accepted athep source>.`, recorded in the spec.
- **Printer repairs:** they make the basic readiness and the fully nonpreemptive job model explicit in
  `valid_schedule`, `work_conserving` and `respects_JLFP_policy_at_preemption_point`, as in the accepted EDF files.

## Validation

- **Spec** `results_rta_ideal_edf_fully_nonpreemptive.json`; base run `results_rta_ideal_edf_bounded_nps`.
- **Export root:** the base root plus the statement.
- **Export:** 154,565 lines.

Certificate chain (53 modules):
- **The accepted ideal replay chain**, with the replayed `PreemptionTimeCorrespondence` and `EdfAthepBoundCorrespondence`
  and `IdlStateRel`, regenerated at this export with no block dropped.
- **`RtaIdealEdfFullyNonpreemptiveCorrespondence.v`:**
  - **Helper part:** the accepted ideal helper part, without the helpers naming the ideal interference instances (not
    in this export; not used). The header records the drop.
  - **As in the accepted ideal EDF `bounded_nps` certificate:** the task-set predicates, the EDF policy, basic
    readiness, the policy at preemption points, the `bounded_pi` / `bounded_nps` search-space definitions, the
    conditional maximum and `blocking_relevant`.
  - **The fully nonpreemptive job model relation and the `nonpreemptive_schedule` relation** at the related schedule
    pair.
  - **The correspondence:** over the accepted RBF, blocking-bound, athep-bound, validity, work-conservation and
    response-time-bound relations.

No source or target theorem is used.

Attempts: prepare attempt 1 passed; finalization 1 was accepted.

Audit: 20 certificates, 15 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 5 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **333 / 357 files**, **2122 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
