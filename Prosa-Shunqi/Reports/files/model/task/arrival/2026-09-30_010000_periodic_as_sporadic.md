# model/task/arrival/periodic_as_sporadic.v — canonical translation report

First experiment timestamp: **2026-09-30 01:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/task/arrival/periodic_as_sporadic.v`; rank 186.
- Public declarations: **5**:
  - the global instance `periodic_as_sporadic`;
  - `valid_period_is_valid_inter_arrival_time`;
  - `periodic_task_respects_sporadic_task_model`;
  - `valid_periods_are_valid_inter_arrival_times`;
  - `periodic_task_sets_respect_sporadic_task_model`.
- Dependency `model/task/arrival/periodic.v`: accepted.

## Translation

`Prosa/Model/Task/Arrival/PeriodicAsSporadic.lean`.
- The source global instance is a Lean `instance` of the same name, `⟨task_period⟩`. The statements find it by instance resolution, as the elaborated types do.
- `TaskSet Task` is the accepted `List Task`.

Proofs:
- The two validity remarks are definitional.
- `periodic_task_respects_sporadic_task_model` follows the source:
  - distinct jobs of the task have distinct indices (accepted `diff_jobs_iff_diff_indices`);
  - the earlier-arriving job has the smaller index, because otherwise its periodic predecessor would arrive no earlier than the other job, contradicting the positive period (accepted `index_lte_implies_arrival_lte`);
  - the later job's periodic predecessor then separates the two arrivals by at least one period.

Lean axioms: none beyond the standard ones.

## Source binding

The instance is a byte-identical computational block. The statements are extracted from the authoritative elaborated types (module `PeriodicAsSporadicSemanticSource`).
- The periodic import is bound to the accepted extracted periodic source, which is hash-checked as the base.
- `model/task/arrival/sporadic.v` is compiled from the pinned tree.

All 5 fingerprints match the evidence.

## Validation

Spec `model_task_arrival_periodic_as_sporadic.json`; base run `model_task_arrival_periodic_final`. The accepted `Sporadic` `.olean` is copied and hash-checked.

Attempts:
- `attempt1_instance_axiom_audit_missing`: the Lean type audit printed axioms only for the theorems, not for the instance.
- `attempt2_instance_fingerprint_missing`: the statement probe had no `Check @periodic_as_sporadic` block for the computational declaration.
- Both fixtures were completed; no statement changed.
- The final export has 30,110 lines.

Certificate chain:
- The accepted ArrivalsSeq*/Arrivals/Periodic certificates, re-bound.
- The new `PeriodicAsSporadicCorrespondence.v`:
  - The instance is related by its observable field, `task_min_inter_arrival_time = task_period`, under the accepted `PerRel`.
  - `valid_task_min_inter_arrival_time`, `valid_taskset_inter_arrival_times` and `respects_sporadic_task_model` replay the accepted sporadic-as-curve proofs at the instance.
  - The periodic predicates use the accepted periodic certificate.
  - Task sets are covered in both directions.
  - No source or target theorem is used.

Audit: 11 certificates (5 principal, 6 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. Unobserved aliases were pruned.

## Formal acceptance

Coverage **176 / 357 files**, **1223 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
