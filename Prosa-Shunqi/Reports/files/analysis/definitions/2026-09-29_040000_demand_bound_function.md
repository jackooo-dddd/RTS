# analysis/definitions/demand_bound_function.v — canonical translation report

First experiment timestamp: **2026-09-29 04:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/definitions/demand_bound_function.v`; rank 163.
- Public declarations: **2**:
  - `task_demand_bound_function`;
  - `total_demand_bound_function`.
- Dependency `analysis/definitions/request_bound_function.v`: accepted.

## Translation

`Prosa/Analysis/Definitions/DemandBoundFunction.lean`. Conventions:
- The local `let delta' := delta - (task_deadline tsk - 1)` is kept as a Lean `let`.
- `\sum_(tsk <- ts) F tsk` is the accepted `sumSeq ts F`.
- The binder order follows the elaborated types: TaskCost, TaskDeadline, MaxArrivals.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `DemandBoundFunctionSemanticSource`), with both definitions as byte-identical computational blocks. The `request_bound_function` import is bound to the accepted extracted RBF source (`RequestBoundFunctionSemanticSource`), and its `.vo` is hash-checked against the RBF manifest. Both definitions match the evidence.

## Validation

Spec `analysis_definitions_demand_bound_function.json`; base run `analysis_definitions_request_bound_function_final`.

The export has 135,659 lines. It is the accepted RBF export root (preemption-parameter closure, reused verbatim so that the accepted chain applies), plus the two definitions and the `TaskDeadline` class.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter certificates and the accepted `RequestBoundFunctionCorrespondence`, all re-bound.
- The new `DemandBoundFunctionCorrespondence.v`:
  - `TaskDeadline` is related pointwise by `SubNatRel`.
  - The shifted window uses the accepted Nat subtraction.
  - The RBF and the sequence sum use the accepted RBF certificates.
  - No source or target proof is used.

Audit: 2 principal certificates, both certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`.

The audit observed two aliases of the re-bound RBF module, `RequestBoundFunctionCorrespondence.I.{True,HEq_inst1}`. These were added to the allowlist, and every unobserved alias was pruned.

## Formal acceptance

Coverage **155 / 357 files**, **1128 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
