# analysis/facts/sporadic/arrival_sequence.v — canonical translation report

First experiment timestamp: **2026-09-29 02:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/sporadic/arrival_sequence.v`; rank 152.
- Public declarations: **7**:
  - `size_task_arrivals_at_leq_one`;
  - `only_j_in_task_arrivals_at_j`;
  - `only_j_at_job_arrival_j`;
  - `index_j_in_task_arrivals_at`;
  - `prev_job_arr_lt`;
  - `task_arrivals_at_as_task_arrivals_between`;
  - `prev_job_cat`.
- Dependency `analysis/facts/sporadic/arrival_times.v`: accepted.

## Translation

`Prosa/Analysis/Facts/Sporadic/ArrivalSequence.lean`. Conventions:
- `size` is `length` and `index` is `List.idxOf`.
- `~ P` is `¬ P`.
- The Boolean validity hypothesis is `= true`.

The statement hypothesis sets follow the elaborated types; `omit [SporadicModel Task]` is used where the elaborated type lacks it.

The proofs use the accepted Lean facts:
- the sporadic separation;
- `job_in_arrivals_at`;
- `arrivals_uniq` nodup;
- `prev_job_*` and `no_jobs_between_consecutive_jobs`;
- `task_arrivals_cat` and `task_arrivals_between_cat`;
- `uneq_job_uneq_arr`.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `FactsSporadicArrivalSequenceSemanticSource`), with the statements taken from the authoritative elaborated types. The proof-heavy `arrival_times` import is dropped. All 7 statements match the evidence.

One statement matches modulo the display parentheses of `~ (exists …)`. The pipeline's existing exists-parenthesis allowance, previously covering `\/` and `<->`, now also covers `~`.

## Validation

Spec `analysis_facts_sporadic_arrival_sequence.json`; base run `analysis_facts_sporadic_arrival_times_final`.

The export has 30,083 lines: the accepted arrival-times export root without its theorems, plus the seven statements.

Certificate chain:
- The accepted ArrivalsSeq*/Arrivals certificates, re-bound.
- The new `FactsSporadicArrivalSequenceCorrespondence.v`:
  - Task arrivals, `job_index`, `prev_job`, `size`, `index`, singleton lists and concatenation use the accepted arrival-sequence certificates.
  - The sporadic-model propositions and the logical connectives are replayed from the accepted sporadic certificates.
  - The `¬ ∃` uses an identity-carrier existential.
  - No source or target theorem is used.

Audit: 15 certificates (7 principal, 8 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. Unobserved aliases were pruned.

## Formal acceptance

Coverage **153 / 357 files**, **1119 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
