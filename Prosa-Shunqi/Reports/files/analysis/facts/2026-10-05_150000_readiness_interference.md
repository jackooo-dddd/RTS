# analysis/facts/readiness_interference.v — canonical translation report

First experiment timestamp: **2026-10-05 15:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/readiness_interference.v`; layer 20; rank 226.
- Public declarations: **2** statements. If no higher-or-equal-priority job is ready:
  - there is no interference from another higher-or-equal-priority job (`no_hep_ready_implies_no_another_hep_interference`);
  - there is no readiness-aware service inversion (`no_hep_ready_implies_no_service_inversion`).
- Dependencies (all accepted):
  - `analysis/definitions/readiness_interference.v`;
  - `analysis/facts/priority/classes.v`;
  - `analysis/facts/interference.v`;
  - `analysis/definitions/service_inversion/readiness_aware.v` (accepted in this session).

## Translation

`Prosa/Analysis/Facts/ReadinessInterference.lean`. Both statements are proved in Lean.
- **First statement:** a served job receives service, so it is scheduled (the accepted `service_at_implies_scheduled_at`). A valid schedule then makes it ready. So a served higher-or-equal-priority job would witness `some_hep_job_ready`.
- **Second statement:** unfolds the readiness-aware conjunction.
- **Binders** follow the elaborated source types; the unused validity of the arrival sequence is absent. The first statement quantifies the JLFP policy after the valid-schedule hypothesis, as the source does.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `FactsReadinessInterferenceSemanticSource`: the two statements are the authoritative elaborated types, with proofs omitted.
- **Interference definitions:** bound to the accepted extracted `InterferenceSemanticSource`. Its `.vo` is copied from the accepted run and hash-checked against its manifest. `model/aggregate/workload` is compiled from the pinned tree; the result is byte-identical to that run's `.vo`, checked before use.
- **Readiness-aware definitions:** bound to the accepted extracted `ReadinessAwareSemanticSource` through a recorded module alias `readiness_aware`; the elaborated statement prints `readiness_aware.service_inversion`.
- **Dropped:** the proof-only facts imports.

The fingerprints match both statements (bodies equal to the elaborated types).

## Validation

- **Spec** `analysis_facts_readiness_interference.json`; base run `analysis_definitions_service_inversion_readiness_aware`.
- **Export root:** the base root merged with the accepted interference root; the arrivals and interference fixtures are added.
- **Export:** 138,894 lines; Rocq import in 43 s.

Certificate chain:
- the accepted readiness-aware chain;
- the accepted `ArrivalsCorrespondence` and `InterferenceCorrespondence`, re-bound;
- `FactsReadinessInterferenceCorrespondence.v`.

Certificate:
- **Input relations**, as for readiness-aware service inversion:
  - processor states by the accepted Service relations of both certificate generations over the same state pair;
  - schedules, job-arrival, job-cost and readiness instances, and arrival sequences by the accepted relations.
- **The JLFP policy:** quantified inside the first statement and covered in both directions by the accepted import/export maps.
- **`valid_schedule`:** related through the accepted `scheduled_at`, `arrives_in` and readiness relations.
- **Predicates:** through the accepted `some_hep_job_ready`, `another_hep_job_interference` and readiness-aware `service_inversion` correspondences.

No source or target theorem is used.

Attempts:
- **Certificate compile:** the scheduled-in relation had to be named with its JitterSvc module qualifier.
- **Finalization attempt 1** stopped at the assumption audit (log archived). Findings:
  - the `ReadinessAwareCorrespondence.I.{True,HEq,HEq_inst1}` helper aliases;
  - `JitterSvcScheduleOperations.SvcSourceTrue`.
- **`SvcSourceTrue`** is the accepted SProp truth type of the JitterSvc schedule operations, reported as relying on definitional UIP. It is already allowlisted unqualified, and its module-qualified form appears only because both Service generations are loaded. The same class is already allowlisted in module-qualified form (`ServiceScheduleOperations.SvcSourceTrue`). Exactly this qualified name was added to the UIP allowlist, together with the aliases.
- **Finalization attempt 2** was accepted.

Audit: 6 certificates (the two statements and four helpers), 5 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 1 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected_assumptions=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **312 / 357 files**, **1942 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
