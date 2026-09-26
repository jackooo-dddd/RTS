# model/task/preemption/fully_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-09-28 18:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/task/preemption/fully_nonpreemptive.v`; rank 158.
- Public declarations: **1**: `fully_nonpreemptive_task_model`.
- The section-local `#[local] Instance fully_nonpreemptive_rtc_threshold` is also translated and certified.
- Dependency `model/task/preemption/parameters.v`: accepted.

## Translation

`Prosa/Model/Task/Preemption/FullyNonpreemptive.lean`. The task model maps each task to its cost; the local threshold is `constant ε`, i.e. `fun _ => 1`. Both are `@[reducible]` definitions of class type, which later translations enable locally.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `TaskPreemptionFullyNonpreemptiveSemanticSource`). The definition and the helper block `fully_nonpreemptive_rtc_threshold` are byte-identical and emitted in source order. The `parameters.v` import is bound to the accepted extracted source, whose `.vo` is hash-checked. The extraction re-imports `prosa.util.notation` after MathComp, so that `constant` resolves to Prosa's definition rather than MathComp's `seq.constant`, matching the source import order. Archived attempt: `_attempt1_constant_shadowed`. The fingerprint matches the evidence.

## Validation

Spec `model_task_preemption_fully_nonpreemptive.json`; base run `model_task_preemption_parameters_final`. The export has about 135.6k lines: the accepted task-preemption-parameters export root reused verbatim, plus the two definitions.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter/TaskPreemptionParameters certificates, re-bound.
- The new `TaskPreemptionFullyNonpreemptiveCorrespondence.v`: The task model is related through `Htc` and the local instance through the constant `1`.

Audit: 2 certificates (1 principal, 1 helper). Both are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. Unobserved aliases were pruned.

## Formal acceptance

Coverage **145 / 357 files**, **1086 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
