# model/task/preemption/limited_preemptive.v — canonical translation report

First experiment timestamp: **2026-09-28 20:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/task/preemption/limited_preemptive.v`; rank 160.
- Public declarations: **8**:
  - `task_beginning_of_execution_in_preemption_points`;
  - `task_end_of_execution_in_preemption_points`;
  - `nondecreasing_task_preemption_points`;
  - `consistent_job_segment_count`;
  - `job_respects_segment_lengths`;
  - `task_segments_are_nonempty`;
  - `valid_fixed_preemption_points_task_model`;
  - `valid_fixed_preemption_points_model`.
- The section-local `#[local] Instance limited_preemptions_rtc_threshold` is also translated and certified.
- Dependencies `model/preemption/limited_preemptive.v` and `model/task/preemption/parameters.v`: accepted.

## Translation

`Prosa/Model/Task/Preemption/LimitedPreemptive.lean`. Conventions:
- `tsk \in ts` is `decide (tsk ∈ ts) = true`.
- `size s` is `s.length`, and `nth 0 s n` is `s.getD n 0`.
- `ε` is `1`.
- `first0`, `last0`, `distances` and `nondecreasing_sequence` are the accepted utilities.
- The local threshold is `@[reducible]`.
- Binder orders follow the elaborated types.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `TaskLimitedPreemptiveSemanticSource`). The eight definitions and the helper block are byte-identical and emitted in source order. The two imports are bound to their accepted extracted sources:
- `TaskPreemptionParametersSemanticSource`, hash-checked through `base_checks`;
- `LimitedPreemptiveSemanticSource`, a hash-checked `extra_artifact` whose rebuilt Lean olean matches its manifest.

Recorded local notations reconnect `arr_seq` and `ts`. All 8 fingerprints match the evidence.

## Validation

Spec `model_task_preemption_limited_preemptive.json`; base run `model_task_preemption_parameters_final`. The export has 136,202 lines: the union of the accepted task-preemption-parameters and limited-preemptive export roots, plus the declarations and `first0`.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter/LimitedPreemptive/TaskPreemptionParameters certificates, re-bound.
- The new `TaskLimitedPreemptiveCorrespondence.v`:
  - `first0` is related by case analysis.
  - `last0`, `size`, zero-defaulted `nth`, `distances` and `nondecreasing_sequence` use the accepted lemmas.
  - The job-level validity uses the accepted `valid_limited_preemptions_job_model_correspondence`.
  - The local threshold uses the accepted `task_last_nonpr_segment_correspondence`.

Audit: 12 certificates (8 principal, 4 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. Unobserved aliases were pruned.

## Formal acceptance

Coverage **147 / 357 files**, **1095 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
