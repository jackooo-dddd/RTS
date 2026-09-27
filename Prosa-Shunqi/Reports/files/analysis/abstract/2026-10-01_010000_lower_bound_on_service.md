# analysis/abstract/lower_bound_on_service.v — canonical translation report

First experiment timestamp: **2026-10-01 01:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/abstract/lower_bound_on_service.v`; rank 210.
- Public declarations: **3**: `interference_is_complement_to_schedule`, `service_and_interference_bounded`, `j_receives_enough_service`.
- Dependencies `analysis/abstract/busy_interval.v`, `analysis/abstract/definitions.v`, `analysis/facts/model/service_of_jobs.v` and `analysis/facts/preemption/rtc_threshold/job_preemptable.v`: accepted.

## Translation

`Prosa/Analysis/Abstract/LowerBoundOnService.lean`. Binders follow the elaborated types: each lemma takes only the inputs and hypotheses it uses, in their elaborated order. The unused task-cost and preemption context and the arrival hypotheses are absent from the elaborated types, so they are absent here too.

Proofs follow the source:
- `interference_is_complement_to_schedule` and `service_and_interference_bounded`: pointwise work conservation, summed over `[t, t + δ)` against `sum_of_ones`. The upper bound also uses the unit-service model.
- `j_receives_enough_service`: if `t1 + δ` lies inside the busy interval, the result follows from the complement lemma. Otherwise it follows from the job completing within the busy interval (`job_completes_within_busy_interval`), using `service_cat`.

Lean axioms: none beyond the standard ones.

## Source binding

The statements come from the authoritative elaborated types (module `LowerBoundOnServiceSemanticSource`).
- The statements mention the abstract definitions, `job_cost_positive` and `unit_service_proc_model`, all compiled from the pinned tree of the base closure.
- The proof-only imports (service-of-jobs facts, job-preemptable facts, abstract busy interval) are dropped.

All 3 statements match the evidence. As for `busy_interval.v`, the official display qualifies the abstract notions (`definitions.busy_interval_prefix`, `definitions.work_conserving`); the probe reproduces this with display-only shadows.

## Validation

Spec `analysis_abstract_lower_bound_on_service.json`; base run `analysis_abstract_busy_interval_final`.

Export: 137,832 lines. The export root is the accepted abstract busy-interval root (the busy-prefix root merged with the workload root) plus the three statements.

Attempts:
- `attempt1_missing_import_wrapper`: the run was rejected because the certificate directory lacked the `ImportedLowerBoundOnService.v` wrapper. I added the wrapper and archived the run.

Certificate chain:
- The accepted abstract-definitions family (Service*/AbstractDefinitions* and the busy-interval helpers).
- The accepted ArrivalsSeq*/Arrivals/Workload certificates.
- The new `LowerBoundOnServiceCorrespondence.v`:
  - Jobs are identity; instants and durations are related by `SubNatRel`. Processor states are covered in both directions for `unit_service_proc_model`.
  - Work conservation and the abstract busy interval (and its prefix) are related by the accepted abstract certificates. Service, service during an interval and cumulative interference are related by the accepted service and abstract-sum certificates.
  - No source or target theorem is used.

Audit: the published audit covers the 3 principal certificates. All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`; their `Print Assumptions` closures include the helpers they use. The published run omitted the separate helper audits because of a wrong helper-prefix argument. A follow-up check-only run with the corrected prefix audited all 7 (3 principal, 4 `lbs_*` helpers) and passed with the same result. The publication itself was not changed.

## Formal acceptance

Coverage **200 / 357 files**, **1395 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
