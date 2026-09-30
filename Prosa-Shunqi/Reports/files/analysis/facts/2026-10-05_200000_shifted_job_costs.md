# analysis/facts/shifted_job_costs.v — canonical translation report

First experiment timestamp: **2026-10-05 20:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/shifted_job_costs.v`; layer 26; rank 282.
- Public declarations: **3**:
  - `job_costs_shifted`: for `j` arriving after `O_max`, a job `j'` arriving in `[O_max + HP, O_max + 2HP)`
    gets the cost of its corresponding job in `j`'s hyperperiod;
  - the section-local instance `job_costs_in_oi`;
  - the lemma `job_costs_shifted_valid`: the shifted costs are valid.
- Dependencies (accepted): `analysis/facts/hyperperiod.v` (accepted in this session),
  `analysis/facts/periodic/{arrival_times,task_arrivals_size}.v`, `model/task/concept.v`.

## Translation

`Prosa/Analysis/Facts/ShiftedJobCosts.lean`:
- **Representation:**
  - the source's Boolean `if` is `bif`;
  - `a <= b < c` is `decide (a ≤ b) && decide (b < c)`;
  - `O_max` and `HP` are unfolded;
  - `job_costs_in_oi` is a named reducible definition of the job-cost class, passed explicitly where the source's
    statement uses the section-local instance.
- **The proof:** in the shifted branch, the corresponding job has the same task (`corresponding_jobs_have_same_task`)
  and arrives (`corresponding_job_arrives`), so the given job-cost validity applies; otherwise the original cost is
  kept.
- Lean axioms: only the standard ones.

## Source binding

Extract mode, module `ShiftedJobCostsSemanticSource`:
- the two definitions are byte-identical computational blocks (`EXACT_HASH`), with the recorded local binding
  `job_costs_shifted=job_costs_shifted arr_seq ts j` for the instance's use inside the section;
- the statement is the authoritative elaborated type (`STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`).

Its conclusion uses the section-local instance implicitly.
- **Without a repair**, the extracted statement resolved the job-cost class to the section's original instance. The
  fingerprint gate rejected this (`forall j : Job` printed as an unused `Job ->`).
- **With a recorded printer repair**, the conclusion names `@job_costs_in_oi … arr_seq ts j` explicitly. This follows
  the accepted `analysis/facts/suspension.v` precedent, and the fingerprint then matches.

## Validation

- **Spec** `analysis_facts_shifted_job_costs.json`; base run `analysis_facts_hyperperiod`.
- **Export root:** the base root plus the definitions, the statement and the task-concept validity predicates.
- **Export:** 138,077 lines; Rocq import in 43 s.
- **Certificate chain:** the accepted hyperperiod-definitions and infinite-jobs chain (re-bound;
  `FactsHyperperiodCorrespondence` is not needed and was removed from the copy) and
  `ShiftedJobCostsCorrespondence.v`.

Input relations:
- task-offset, periodic-model, task-cost, `job_task` (`Lean.eq`), job-arrival, job-cost and arrival-sequence inputs by
  the accepted relations;
- tasks and jobs are identity carriers;
- task sets are covered inside the statement.

How each piece is related:
- **`job_costs_shifted`:** the condition through the accepted `&&`, `<=`, `<`, addition, multiplication and
  hyperperiod relations; the shifted branch through the accepted `corresponding_job_in_hyperperiod` relation; the
  source `if` and the Lean `cond` by case analysis on the related Booleans.
- **The statement:** relates the job-cost validity of both instances and the periodic task set, periods, offsets,
  `infinite_jobs` and `all_jobs_from_taskset` through the accepted certificates.

No source or target theorem is used.

Audit: 7 certificates (3 declarations and 4 helpers), 6 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 1 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- no allowlist change;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **315 / 357 files**, **1961 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
