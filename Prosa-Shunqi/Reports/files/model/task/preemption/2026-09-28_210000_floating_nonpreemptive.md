# model/task/preemption/floating_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-09-28 21:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/task/preemption/floating_nonpreemptive.v`; rank 157. It is processed after rank 160, whose run it uses as its base.
- Public declarations: **2**: `job_respects_task_max_np_segment` and `valid_model_with_floating_nonpreemptive_regions`.
- The section-local `#[local] Instance floating_preemptive_rtc_threshold` is also translated and certified.
- Dependencies `model/preemption/limited_preemptive.v` and `model/task/preemption/parameters.v`: accepted.

## Translation

`Prosa/Model/Task/Preemption/FloatingNonpreemptive.lean`. The source enables the job-level `limited_preemptive_job_model` with `#[local] Existing Instance`; the Lean definitions pass the accepted Lean definition explicitly, as the elaborated source does. The local threshold is the task cost, as a `@[reducible]` definition.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `TaskFloatingNonpreemptiveSemanticSource`):
- The two definitions and the helper block are byte-identical and emitted in source order.
- Both imports are bound to their accepted extracted sources, whose `.vo` files are hash-checked by `base_checks`.
- The source's `#[local] Existing Instance limited_preemptive_job_model` is replayed after the imports.
- A recorded local notation reconnects `arr_seq`.

Both fingerprints match the evidence.

## Validation

Spec `model_task_preemption_floating_nonpreemptive.json`; base run `model_task_preemption_limited_preemptive_final`.

The export has 135,883 lines: the accepted task-level limited-preemptive export root without its own targets, plus the declarations.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter/LimitedPreemptive/TaskPreemptionParameters certificates, re-bound.
- The new `TaskFloatingNonpreemptiveCorrespondence.v`:
  - The two job models are related by the accepted `lp_limited_preemptive_job_model_related`.
  - The maximum nonpreemptive segment and job-level validity use the accepted parameter and limited-preemptive certificates.
  - The task bound uses `TppMaxSegmentRel`.

Audit: 4 certificates (2 principal, 2 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. Unobserved aliases were pruned.

## Formal acceptance

Coverage **148 / 357 files**, **1097 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
