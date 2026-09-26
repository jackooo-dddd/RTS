# analysis/definitions/request_bound_function.v — canonical translation report

First experiment timestamp: **2026-09-28 12:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/definitions/request_bound_function.v`; rank 143.
- Public declarations: **6**:
  - `task_request_bound_function`;
  - `total_request_bound_function`;
  - `total_{hep,ohep,ep,hp}_request_bound_function_FP`.
- Dependencies `model/task/arrival/curves.v`, `model/priority/classes.v`, `analysis/facts/priority/classes.v` and `util/sum.v`: accepted.

## Translation

`Prosa/Analysis/Definitions/RequestBoundFunction.lean`:
- The task RBF is `task_cost tsk * max_arrivals tsk Δ`.
- Totals use the accepted `sumSeq`, and the filtered totals use `sumFiltered`, with the predicates:
  - `hep_task o tsk`;
  - `hep_task o tsk && decide (o ≠ tsk)`;
  - `ep_task o tsk`;
  - `hp_task o tsk`.
- The FP policy is an instance binder, following the elaborated types.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `RequestBoundFunctionSemanticSource`), as byte-identical blocks. The proof-only `analysis/facts/priority/classes` and `util/sum` imports are dropped: the definitions use only MathComp big operators plus `curves` and `classes`, which are the compiled pinned sources of the base run. All 6 fingerprints match the evidence.

## Validation

Spec `analysis_definitions_request_bound_function.json`; base run `model_preemption_parameter_final`.

The export has 135,526 lines. The diagnosis: the accepted preemption-parameter export root is reused verbatim. It adds the six definitions, `sumSeq`/`sumFiltered` with five kernel-checked constructor equations (universe-polymorphic), `hp_task`/`ep_task` and the task classes.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter certificates, re-bound.
- The new `RequestBoundFunctionCorrespondence.v`:
  - MathComp's plain and filtered sequence sums are related to `sumSeq`/`sumFiltered` by induction (`big_nil`/`big_cons` and the exported equations).
  - Multiplication uses the accepted `sub_mul_correspondence`.
  - `!=` uses a decidable-inequality observation.
  - `ep_task` and `hp_task` go through the Boolean connectives.

Audit: 12 certificates (6 principal, 6 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. Unobserved aliases were pruned.

## Formal acceptance

Coverage **139 / 357 files**, **1060 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
