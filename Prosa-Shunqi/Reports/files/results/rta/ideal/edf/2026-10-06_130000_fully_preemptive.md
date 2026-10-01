# results/rta/ideal/edf/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-06 13:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ideal/edf/fully_preemptive.v`; layer 28; no dependents.
- Public declaration: **1** theorem, `uniprocessor_response_time_bound_fully_preemptive_edf`.
- Dependencies (all accepted):
  - `analysis/facts/preemption/{rtc_threshold,task}/preemptive.v`, `analysis/facts/readiness/basic.v`;
  - `model/priority/edf.v`, `model/readiness/basic.v`, `model/task/preemption/fully_preemptive.v`;
  - `results/rta/ideal/edf/bounded_nps.v`.

## Translation

`Prosa/Results/Rta/Ideal/Edf/FullyPreemptive.lean`; it compiles with only the standard Lean axioms.

- **Binders:** follow the elaborated type.
- **Section-local instances:** the basic readiness, the EDF policy (over `job_deadline_from_task_deadline`) and the
  accepted `fully_preemptive_job_model` are passed explicitly.
- **Search space and bounds:** `bounded_nps.is_in_search_space` is the accepted ideal EDF `bounded_nps` definition, and
  `edf_athep_bound.bound_on_athep_workload` is the accepted athep bound.

The proof follows the source. It applies the accepted ideal EDF `bounded_nps` theorem with:
- the fully preemptive job, task and run-to-completion models;
- the accepted fully preemptive model facts;
- the EDF blocking bound, which vanishes in the fully preemptive task model.

## Source binding

Extract mode, module `RtaIdealEdfFullyPreemptiveSemanticSource`. The statement is the authoritative elaborated type;
its fingerprint is `STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`.

Bindings:
- **Base closure (the accepted ideal EDF `bounded_nps` run):** the accepted extracted `bounded_nps`, `bounded_pi`,
  blocking-bound and athep sources, and the accepted fully preemptive task model source.
- **Validation-only module paths:** `Module bounded_nps := <the accepted ideal EDF bounded_nps source>.` and
  `Module edf_athep_bound := <the accepted athep source>.`, recorded in the spec.
- **Printer repairs:** they make the basic readiness and the fully preemptive job model explicit in `valid_schedule`,
  `work_conserving` and `respects_JLFP_policy_at_preemption_point`, as in the accepted EDF files.

## Validation

- **Spec** `results_rta_ideal_edf_fully_preemptive.json`; base run `results_rta_ideal_edf_bounded_nps`.
- **Export root:** the base root plus the statement.
- **Export:** 154,421 lines.

Certificate chain (53 modules):
- **The accepted ideal replay chain**, with the replayed `PreemptionTimeCorrespondence` and `EdfAthepBoundCorrespondence`
  and `IdlStateRel`, regenerated at this export with no block dropped.
- **`RtaIdealEdfFullyPreemptiveCorrespondence.v`:**
  - **Helper part:** the accepted ideal helper part, without the helpers naming the ideal interference instances (not
    in this export; not used). The header records the drop.
  - **As in the accepted ideal EDF `bounded_nps` certificate:** the task-set predicates, the EDF policy, basic
    readiness, the policy at preemption points and the `bounded_pi` / `bounded_nps` search-space definitions.
  - **The fully preemptive job model relation.**
  - **The correspondence:** over the accepted RBF, athep-bound, validity, work-conservation and response-time-bound
    relations.

No source or target theorem is used.

Attempts: prepare attempt 1 passed; finalization 1 was accepted.

Audit: 16 certificates, 11 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 5 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **332 / 357 files**, **2121 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
