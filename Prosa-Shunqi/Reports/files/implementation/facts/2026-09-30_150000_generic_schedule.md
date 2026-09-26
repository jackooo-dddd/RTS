# implementation/facts/generic_schedule.v — canonical translation report

First experiment timestamp: **2026-09-30 15:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/facts/generic_schedule.v`; rank 200.
- Public declarations: **6**: `schedule_up_to_def`, `schedule_up_to_unfold`, `schedule_up_to_widen`, `schedule_up_to_empty`, `schedule_up_to_prefix_inclusion`, `schedule_up_to_identical_prefix`.
- Dependencies `analysis/facts/transform/replace_at.v` and `implementation/definitions/generic_scheduler.v`: accepted.

## Translation

`Prosa/Implementation/Facts/GenericSchedule.lean`. Binders follow the elaborated types, over an arbitrary processor model.

Conventions:
- The section-local `prefix t := if t is t'.+1 then schedule_up_to … t' else empty_schedule …` is inlined as a `match` on the instant, as in the elaborated types.
- `t.+1` is `t + 1`.

Proofs:
- `def`/`unfold`: case analysis on the instant.
- `widen`/`empty`: the replaced instant differs from the observed one; `empty` is by induction.
- `prefix_inclusion`: induction on the horizon with `widen`.
- `identical_prefix`: via `prefix_inclusion`.

Lean axioms: none beyond the standard ones.

## Source binding

The statements are extracted from the authoritative elaborated types (module `FactsGenericScheduleSemanticSource`).
- `implementation/definitions/generic_scheduler` is compiled from the pinned tree, over the base run's pinned `analysis/transform/swap`.
- `analysis/definitions/schedule_prefix` is the compiled pinned source of the base closure.
- The proof-only `facts/transform/replace_at` import is dropped.

All 6 statements match the evidence (fingerprint: 6 checked, 0 mismatches).

## Validation

Spec `implementation_facts_generic_schedule.json`; base run `analysis_facts_transform_replace_at_final`.

Artifacts: the accepted `GenericScheduler` `.olean` from its accepted run is copied and hash-checked.

Export: 133,514 lines. The export root:
- is the accepted replace-at export root without its statements (Service / Schedule closure with the kernel-checked `replace_at` case equations);
- adds the generic scheduler;
- adds kernel-checked equations for `schedule_up_to` (zero/successor) and `empty_schedule`;
- adds the six statements.

Attempts: none failed. Before the certificate compiled, a few fixes were needed:
- `by` was avoided, because it calls the recursive `done` of the approved tactics patch;
- Lean-scope `0` patterns were written as `O`;
- both statements use the same Lean matcher.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc* certificates, re-bound.
- The new `FactsGenericScheduleCorrespondence.v`:
  - Statements are specialised at their leading inputs: the job type, the accepted two-sided `SvcProcessorStateRel`, the pointwise policy and the idle state.
  - The policy is related, through the state conversion, on schedules related through the state conversion and related instants. The idle state is related through the state conversion. Instants are covered in both directions.
  - `empty_schedule` and `replace_at` are related by the exported equations; `schedule_up_to` by induction.
  - The Lean matcher on instants reduces on the canonical Nat constructors.
  - No source or target theorem is used.

Audit: 17 certificates (6 principal, 11 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`.

## Formal acceptance

Coverage **190 / 357 files**, **1340 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
