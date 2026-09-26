# model/task/preemption/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-09-28 19:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/task/preemption/fully_preemptive.v`; rank 159.
- Public declarations: **1**: `fully_preemptive_task_model`.
- The section-local `#[local] Instance fully_preemptive_rtc_threshold` is also translated and certified.
- Dependency `model/task/preemption/parameters.v`: accepted.

## Translation

`Prosa/Model/Task/Preemption/FullyPreemptive.lean`. The task model is `fun _ => 1` (ε); the local threshold is the task cost. Both are `@[reducible]` definitions of class type, which later translations enable locally.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `TaskPreemptionFullyPreemptiveSemanticSource`). The definition and the helper block `fully_preemptive_rtc_threshold` are byte-identical and emitted in source order. The `parameters.v` import is bound to the accepted extracted source, whose `.vo` is hash-checked.  The fingerprint matches the evidence.

## Validation

Spec `model_task_preemption_fully_preemptive.json`; base run `model_task_preemption_parameters_final`. The export has about 135.6k lines: the accepted task-preemption-parameters export root reused verbatim, plus the two definitions.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter/TaskPreemptionParameters certificates, re-bound.
- The new `TaskPreemptionFullyPreemptiveCorrespondence.v`: The task model is related through the constant `1` and the local instance through `Htc`.

Audit: 2 certificates (1 principal, 1 helper). Both are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. Unobserved aliases were pruned.

## Formal acceptance

Coverage **146 / 357 files**, **1087 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
