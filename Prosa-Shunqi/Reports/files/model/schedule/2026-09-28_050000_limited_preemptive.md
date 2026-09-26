# model/schedule/limited_preemptive.v — canonical translation report

First experiment timestamp: **2026-09-28 05:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/schedule/limited_preemptive.v`; rank 135.
- Public declarations: **1**: `schedule_respects_preemption_model`.
- Dependency `model/preemption/parameter.v`: accepted.

## Translation

`Prosa/Model/Schedule/LimitedPreemptive.lean`: `∀ j t, arrives_in arr_seq j → (!job_preemptable j (service sched j t)) = true → scheduled_at sched j t = true`.

The binder order follows the elaborated type (`Job`, `PState`, `JobPreemptable`, `arr_seq`, `sched`). Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `ScheduleLimitedPreemptiveSemanticSource`), as a byte-identical block. The `parameter.v` import is bound to the accepted extracted `PreemptionParameterSemanticSource`, whose `.vo` is hash-checked. The fingerprint matches the evidence.

## Validation

Spec `model_schedule_limited_preemptive.json`; base run `model_preemption_parameter_final`.

The export has 134,874 lines. The diagnosis: the accepted preemption-parameter export root is reused verbatim, so that the accepted chain, including the accepted `PreemptionParameterCorrespondence`, applies.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameterCorrespondence modules, re-bound.
- The new `ScheduleLimitedPreemptiveCorrespondence.v`:
  - `arrives_in` is related by the accepted arrival-sequence certificate.
  - `job_preemptable` is related by `PpJobPreemptableRel`.
  - Service and `scheduled_at` are related by the accepted `pp_service_related` and `pp_scheduled_at_related`.

Audit: 1 certificate, certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. The observed aliases `PreemptionParameterCorrespondence.I.{True,HEq,HEq_inst1}` were added to the allowlist.

## Formal acceptance

Coverage **132 / 357 files**, **1027 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
