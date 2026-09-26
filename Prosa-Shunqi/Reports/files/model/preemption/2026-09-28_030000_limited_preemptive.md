# model/preemption/limited_preemptive.v — canonical translation report

First experiment timestamp: **2026-09-28 03:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/preemption/limited_preemptive.v`; rank 132.
- Public declarations: **5**:
  - `JobPreemptionPoints` (class);
  - `beginning_of_execution_in_preemption_points`;
  - `end_of_execution_in_preemption_points`;
  - `preemption_points_is_nondecreasing_sequence`;
  - `valid_limited_preemptions_job_model`.
- The source also declares the section-local `#[local] Instance limited_preemptive_job_model`. It is not a public declaration, but it is translated and certified too.
- Dependency `model/preemption/parameter.v`: accepted.

## Translation

`Prosa/Model/Preemption/LimitedPreemptive.lean`:
- `JobPreemptionPoints` is a class with the field `job_preemptive_points : Job → List work`.
- The local instance is a plain `@[reducible] def limited_preemptive_job_model : JobPreemptable Job`, with `job_preemptable j ρ := decide (ρ ∈ job_preemptive_points j)`. Later translations enable it locally.
- `ρ \in s` in `Prop` position is `decide (ρ ∈ s) = true`.
- `last0` and `nondecreasing_sequence` are the accepted utilities.
- The unused section context `JobArrival` is absent.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `LimitedPreemptiveSemanticSource`). The class, the helper block `limited_preemptive_job_model` and the four definitions are byte-identical blocks.

Two additions to the extraction:
- **New opt-in flag `source_order`.** Blocks are emitted in source order, because the helper instance mentions the class declared before it. The flag was added to `extract_v06_semantic_source.py` (`--source-order`) and the pipeline; existing specs are unaffected.
- **Recorded local notations.** The Section variable `arr_seq` is implicit in the three component uses inside `valid_limited_preemptions_job_model`, so it is reconnected by recorded local notations.

The `parameter.v` import is bound to the accepted extracted `PreemptionParameterSemanticSource`, whose `.vo` is hash-checked. All 5 fingerprints match the evidence.

## Validation

Spec `model_preemption_limited_preemptive.json`; base run `model_preemption_parameter_final`.

The export has 135,039 lines. The diagnosis: the accepted preemption-parameter export root (the Service/Schedule interface closure, about 127k lines) is reused verbatim so that the accepted JitterSvc/Arrivals chain applies. It adds the five declarations, the local instance, `nondecreasing_sequence` and `NondecreasingInterface.nthD`.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc* modules, re-bound.
- The new `LimitedPreemptiveCorrespondence.v`:
  - `JobPreemptionPoints` is related pointwise by `SvcNatListRel`, with two-way totals.
  - Membership and `last0` use the accepted parameter-interface equations.
  - `nondecreasing_sequence` is related through zero-defaulted lookup and length, using the Nondecreasing interface constructor equations and the Nat order correspondences.
  - The local instance is certified as a `JobPreemptable` relation (`lp_limited_preemptive_job_model_related`).

Audit: 23 certificates (2 class totals, 4 definitions, 17 helpers). All are `CERTIFIED` or `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, with `semantic_premises=[]` and `unexpected_assumptions=[]`. The unobserved aliases `SvcTrue` and `SvcSourceTrue` were pruned before publication.

Archived attempts:
- `_attempt1_helper_block_order`;
- `_attempt2_section_variable_uses`;
- `_attempt3_missing_import_stub`.

## Formal acceptance

Coverage **130 / 357 files**, **1025 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
