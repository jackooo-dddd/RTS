# analysis/facts/model/dynamic_suspension.v — canonical translation report

First experiment timestamp: **2026-10-05 13:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/model/dynamic_suspension.v`; layer 18; rank 185.
- Public declarations: **2**:
  - `job_suspension_bounded`: under valid dynamic suspensions, the total suspension of a job of `tsk` within `[t1, t1 + Δ)` is at most `task_total_suspension tsk`;
  - `suspension_of_task_bounded`: the total suspension of the task's jobs arriving in the interval is at most `max_arrivals tsk Δ * task_total_suspension tsk`.
- Dependencies (all accepted): `analysis/facts/model/arrival_curves.v`, `analysis/facts/suspension.v`, `model/task/suspension/dynamic.v` (the latter two accepted in this session).

## Translation

`Prosa/Analysis/Facts/Model/DynamicSuspension.lean`. Both statements are proved in Lean.
- **Per-job bound:** the interval sum of the suspension indicator is split by service level. A suspended job is pending, so its service is below its cost, and only levels `0 … job_cost j - 1` contribute. Each level is bounded by the accepted `suspension_bounded_in_interval`. The sum of the level bounds is `total_suspension j` (the ascending list fold equals the `range` sum), which is at most the task's bound by validity.
- **Per-task bound:** the interval and sequence sums are exchanged. Each job of the task contributes at most the task's bound, and the number of arrivals is at most `max_arrivals tsk Δ` (respects-max-arrivals over `[t1, t1 + Δ)`).
- **Binders** follow the elaborated source types; the unused validity hypotheses of the arrival sequence and the schedule are absent.
- **Representation:** the interval sum is the `Finset.Ico` sum over `Nat`; `\sum_(j <- xs) F j` is `sumSeq xs F`.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `FactsDynamicSuspensionSemanticSource`: the two statements are the authoritative elaborated types, with proofs omitted.
- The accepted extracted suspension and dynamic-suspension modules are bound as base extraction modules.
- `model/task/arrivals` and `model/task/arrival/curves` are compiled from the pinned tree.
- The proof-only facts imports are dropped.

The fingerprints match both statements (bodies equal to the elaborated types).

## Validation

- **Spec** `analysis_facts_model_dynamic_suspension.json`; base run `analysis_facts_suspension`.
- **Export root:** merged with the accepted arrival-curves export root.
- **Additions for the processor-model cover:** the accepted validation-only `ProcessorStateCoverInterface` fixture (`fintypeOfNodupListing`), the core-enumeration `nodup`/`complete` theorems (with proof bodies) and the `supply_on` projection.
- **Normalization:** the two statements are normalized theorem types (the accepted `Nat` `Finset.Ico` projection).
- **Export:** 127,045 lines; Rocq import in 42 s.

Certificate chain:
- the accepted arrivals and curves certificates, re-bound;
- the accepted Service certificates, `ProgressHelpers`, `SuspensionCorrespondence` and `DynamicSuspensionCorrespondence`, re-bound;
- `DsPStateCover.v`;
- `FactsDynamicSuspensionCorrespondence.v`.

`DsPStateCover.v` is a port of the accepted two-way processor-model cover `RsPStateCover.v` (from the ARM/PRM results) to the JitterSvc Service relation modules, whose `SvcProcessorStateRel` record is identical. The supply-on component of the pair, which no statement here needs, is dropped; every other definition and proof is unchanged.

Certificate:
- **Input relations**, each the accepted relation with two-way totals: task-total-suspension, max-arrivals, job-task, job-arrival, job-cost and job-suspension instances.
- **Quantifiers inside the statements** are covered in both directions:
  - processor models, by the ported cover;
  - schedules, by the accepted state-relation roundtrips (pointwise, no function extensionality);
  - arrival sequences, by the accepted canonical map and the list roundtrip;
  - tasks and jobs are identity carriers; instants and durations are covered by `SubNatRel`.
- **Validity:** the accepted `valid_dynamic_suspensions` correspondence.
- **`job_of_task`, `task_arrivals_between`, `respects_max_arrivals`:** the accepted relations.
- **Sums:** through the accepted interval-sum and sequence-sum relations, with the suspension indicator related through the accepted `suspended` relation and `nat_of_bool`/`Bool.toNat`.
- **The product bound:** through the accepted Nat multiplication relation.

No source or target theorem is used.

Attempts:
- **Prepare attempt 1** was stopped and archived (`…_attempt1_missing_cover_fixture`): the root lacked the processor-model cover interface.
- **Prepare attempt 2** was archived (`…_attempt2_missing_supply_on_target`): the export lacked the `supply_on` projection the cover's model construction reads.
- **Prepare attempt 3** passed.
- **Finalization attempt 1** stopped at the assumption audit (log archived as `fdsusp_finalize_attempt1_helper_aliases.log`). The only findings were `DsPStateCover.I.{True,HEq,HEq_inst1}` helper aliases, which were added to the allowlist.
- **Finalization attempt 2** was accepted.

Audit: 10 certificates (the two statements and eight helpers), 8 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 2 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected_assumptions=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **310 / 357 files**, **1937 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
