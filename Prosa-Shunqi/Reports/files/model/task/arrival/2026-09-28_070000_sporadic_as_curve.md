# model/task/arrival/sporadic_as_curve.v — canonical translation report

First experiment timestamp: **2026-09-28 07:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/task/arrival/sporadic_as_curve.v`; rank 137.
- Public declarations: **5**:
  - `MaxArrivalsSporadic` (a `Global Program Instance`);
  - `sporadic_arrival_curve_valid`;
  - `sporadic_task_sets_arrival_curve_valid`;
  - `sporadic_arrival_curve_respects_max_arrivals`;
  - `sporadic_task_sets_respects_max_arrivals`.
- Dependencies `analysis/facts/sporadic/arrival_bound.v`, `model/task/arrival/curves.v` and `util/all.v`: accepted.

## Translation

`Prosa/Model/Task/Arrival/SporadicAsCurve.lean`:
- `MaxArrivalsSporadic` is a Lean global instance, `⟨max_sporadic_arrivals⟩`.
- Validity follows from `div_ceil0` and `div_ceil_monotone1`.
- The respects-max-arrivals results follow from the accepted `sporadic_task_arrivals_bound`.
- The task-set statement names the instance explicitly (`@taskset_respects_max_arrivals … MaxArrivalsSporadic ts`), as the elaborated source does.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `SporadicAsCurveSemanticSource`):
- The instance is a byte-identical block.
- The theorem statements are the authoritative elaborated types.
- The proof-heavy `facts/sporadic/arrival_bound` import is bound to its accepted extracted semantic source, whose `.vo` is hash-checked.

All 5 fingerprints match the evidence.

## Validation

Spec `model_task_arrival_sporadic_as_curve.json`; base run `analysis_facts_sporadic_arrival_bound_final`.

The export has 33,942 lines: the union of the accepted arrival-bound and arrival-curve export roots, without their theorem targets, plus the five declarations.

Certificate chain:
- The accepted ArrivalsSeq*/Arrivals/NatSub/DivMod/Curves certificates, re-bound.
- The new `SporadicAsCurveCorrespondence.v`:
  - The instance is related as a `CvMaxArrivalsRel` curve family.
  - `valid_arrival_curve`, `valid_taskset_arrival_curve`, `respects_max_arrivals` and `taskset_respects_max_arrivals` come from the accepted `CurvesCorrespondence`.
  - The sporadic bound and the sporadic-model inputs are replayed from the accepted arrival-bound certificate.
  - Task sets are covered in both directions (`sac_forall_list`).
  - No source or target theorem is used.

Audit: 12 certificates (5 principal, 7 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. Unobserved inherited aliases were pruned before publication.

Archived attempt: `_attempt1_foreign_statement_only`. That run's export marked the arrival-bound theorems statement-only, which publication rejects. They are no longer exported; the needed helper lemmas are replayed locally instead.

Tooling fix: the generated audit module now sets `Printing Width 1000`, so that long alias names are not wrapped in `Print Assumptions` output.

## Formal acceptance

Coverage **134 / 357 files**, **1033 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
