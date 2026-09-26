# analysis/definitions/priority_inversion.v — canonical translation report

First experiment timestamp: **2026-09-29 06:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/definitions/priority_inversion.v`; rank 164.
- Public declarations: **8**:
  - `priority_inversion`;
  - `priority_inversion_cond`;
  - `cumulative_priority_inversion`;
  - `cumulative_priority_inversion_cond`;
  - `priority_inversion_of_job_is_bounded_by`;
  - `priority_inversion_of_job_cond_is_bounded_by`;
  - `priority_inversion_is_bounded_by`;
  - `priority_inversion_cond_is_bounded_by`.
- Dependencies `analysis/definitions/busy_interval/classical.v` and `analysis/facts/model/scheduled.v`: accepted.

## Translation

`Prosa/Analysis/Definitions/PriorityInversion.lean`. Conventions:
- `x \notin s` is `!decide (x ∈ s)`; `has p s` is `s.any p`; `~~ b` is `!b`.
- The half-open Boolean sum `\sum_(t1 <= t < t2) b t` is `∑ t ∈ Finset.Ico t1 t2, (b t).toNat`.
- Booleans in `Prop` position are `= true`.
- Unused section context is absent; every binder order matches the elaborated types.

Lean axioms: none beyond the standard ones.

## Source binding

The source is bound by extraction (module `PriorityInversionSemanticSource`), with all eight definitions as byte-identical computational blocks.
- The `busy_interval/classical` import is bound to the accepted extracted busy-interval source, and its `.vo` is hash-checked.
- The proof-only `analysis/facts/model/scheduled` import is replaced by the pinned `model/schedule/scheduled` (for `scheduled_jobs_at`) and `model/task/concept`.
- The section variables `arr_seq sched j`, implicit in the section-local uses, are reconnected by recorded local notations.

All 8 definitions match the evidence.

## Validation

Spec `analysis_definitions_priority_inversion.json`; base run `analysis_definitions_busy_interval_classical_final`. `model/schedule/scheduled.v` is pinned, and the accepted `Scheduled.lean` is hash-checked.

The export has 136,013 lines. It is the accepted busy-interval export root without its theorem targets, plus:
- the eight definitions and `scheduled_jobs_at`;
- two source-shaped list-fold projections of the Boolean sums, tied to the compiled definitions by whole-constant `rfl` kernel guards.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter certificates, re-bound.
- The new `PriorityInversionCorrespondence.v`:
  - `scheduled_jobs_at` uses the accepted filter and `arrivals_up_to` certificates.
  - `has`/`List.any` goes by structural reduction.
  - Membership uses `ar_decide_mem_related`.
  - The sums use the accepted interval-sum correspondence through the guarded projections.
  - The busy-interval prefix and quiet time replay the accepted busy-interval proofs.
  - Predicates `P` are related pointwise on Booleans, and the bounds `B` on related Nats.
  - No source or target theorem is used.

Audit: 21 certificates (8 principal, 13 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. Every allowlisted alias was observed.

## Attempts

- `…_attempt1_inherited_type_valued`: the spec inherited the busy-interval `type_valued` field.
- `…_attempt2_missing_local_bindings`: section-local uses needed recorded local notations.

## Formal acceptance

Coverage **157 / 357 files**, **1137 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
