# analysis/facts/periodic/max_inter_arrival.v — canonical translation report

First experiment timestamp: **2026-09-30 09:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/periodic/max_inter_arrival.v`; rank 194.
- Public declarations: **3**:
  - the global instance `max_inter_eq_period`;
  - the remarks `valid_period_is_valid_max_inter_arrival_time` and `periodic_model_respects_max_inter_arrival_model`.
- Dependency `analysis/facts/periodic/arrival_separation.v`: accepted.

## Translation

`Prosa/Analysis/Facts/Periodic/MaxInterArrival.lean`. Conventions:
- The source global instance is a Lean global instance with the same name (`⟨task_period⟩`). The statements find it by instance resolution, as in the elaborated types.
- A Boolean in `Prop` position is `= true`.
- The unused section variable `arr_seq` is absent from the instance, as in the elaborated type.

Proof of `periodic_model_respects_max_inter_arrival_model`:
- The periodic predecessor `j'` of a job with positive index is the required earlier job.
- It is distinct from the job because its index is one less.
- Its arrival plus the period equals the job's arrival.

Lean axioms: none beyond the standard ones.

## Source binding

The instance is extracted as a byte-identical block and the remarks as their authoritative elaborated types (module `FactsPeriodicMaxInterArrivalSemanticSource`).
- The periodic model is bound to its accepted extracted source (`PeriodicSemanticSource`, hash-checked in the base).
- `model/task/arrival/task_max_inter_arrival` is compiled from the pinned tree, as in its accepted run.
- The proof-only `facts/periodic/arrival_separation` import is dropped.

All 3 declarations match the evidence (fingerprint: 3 checked, 0 mismatches).

## Validation

Spec `analysis_facts_periodic_max_inter_arrival.json`; base run `analysis_facts_periodic_arrival_separation_final`.

Artifacts: the accepted `TaskMaxInterArrival` `.olean` is copied and hash-checked.

Export: 30,263 lines. The export root:
- is the accepted periodic arrival-separation export root without its statements;
- is merged with the accepted task-max-inter-arrival root;
- adds the instance and the two statements.

Attempts: no archived failures. The assumption audit first flagged the two `TmiaCorrespondence.I.*` alias names as unexpected. They are the same SProp aliases as for the other re-bound chains; they were added to the alias allow-list and pruned where unobserved.

Certificate chain:
- The accepted ArrivalsSeq*/Arrivals/Periodic/Tmia certificates, re-bound.
- The new `FactsPeriodicMaxInterArrivalCorrespondence.v`:
  - The instance is related by the accepted `TmClassRel`: its field is the period on both sides, related by the accepted `PerRel`.
  - The remarks are specialised at their leading inputs: the periodic model, `job_task` by `Lean.eq`, `job_arrival` by `ArJobArrivalRel`, the arrival sequence and the task. Tasks are identity carriers.
  - `valid_period`, `respects_periodic_task_model`, `positive_task_max_inter_arrival_time` and `valid_task_max_inter_arrival_time` are closed by the accepted certificates at the related instance.
  - No source or target theorem is used.

Audit: 3 certificates (3 principal). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`.

## Formal acceptance

Coverage **184 / 357 files**, **1303 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
