# analysis/facts/model/ideal/priority_inversion.v — canonical translation report

First experiment timestamp: **2026-09-30 19:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/model/ideal/priority_inversion.v`; rank 204.
- Public declarations: **4**: `idle_implies_no_priority_inversion`, `priority_inversion_equiv_sched_lower_priority`, `sched_hep_implies_no_priority_inversion`, `sched_lp_implies_priority_inversion`.
- Dependencies `analysis/facts/model/ideal/schedule.v`, `analysis/facts/priority/inversion.v` and `model/processor/ideal.v`: accepted.

## Translation

`Prosa/Analysis/Facts/Model/Ideal/PriorityInversion.lean`. Binders follow the elaborated types. The unused task, cost and completion context is absent. The JLFP policy, quantified after the schedule hypotheses, is a `∀ [..]` binder. A Boolean in `Prop` position is `= true`, and `~~ b` is `!b`.

Proofs:
- `idle_implies_no_priority_inversion`: the accepted `no_priority_inversion_when_idle`, with `is_idle_def`.
- `priority_inversion_equiv_sched_lower_priority`: `priority_inversion_hep_job` at the ideal uniprocessor model.
- The last two theorems follow from the equivalence.

Lean axioms: none beyond the standard ones.

## Source binding

The statements come from the authoritative elaborated types (module `IdealPriorityInversionSemanticSource`).
- `priority_inversion` is bound to the accepted `PriorityInversionSemanticSource` of the base closure.
- `model/processor/ideal` is compiled from the pinned tree under its accepted proof-only compatibility patch.
- The proof-only facts imports are dropped.

All 4 statements match the evidence (fingerprint: 4 checked, 0 mismatches).

## Validation

Spec `analysis_facts_model_ideal_priority_inversion.json`; base run `analysis_facts_priority_inversion_final`.

Artifacts: the accepted `Ideal.olean` and `Ideal/Schedule.olean` are copied and hash-checked.

Export: 141,682 lines. The export root:
- is the accepted priority-inversion-facts root without its statements;
- adds the accepted ideal-schedule interface: the ideal processor, `ideal_is_idle`, and the kernel-checked ideal-state `scheduled_in` equation;
- adds the four statements;
- adds no new equation.

Attempts:
- `attempt1_missing_ideal_olean_killed`: I stopped this prepare myself after noticing the spec lacked the ideal-processor `.olean` artifact. The artifact was added and the run archived.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter/PriorityInversion certificates, re-bound.
- The new `IdealPriorityInversionCorrespondence.v`. This was the missing `_inst4` ideal-state bridge that had deferred this file.
  - The ideal-state helpers are restated locally: the Option map, the re-proved source closed form of `scheduled_in` against the kernel-checked target equation, and the pointwise schedule relation with two-way covers.
  - JLFP policies are related pointwise on Booleans and covered in both directions.
  - `job_arrival` is related by `ArJobArrivalRel`, and arrival sequences by `ArArrivalSequenceRel`.
  - `priority_inversion` is related through the accepted filter, `arrivals_up_to`, membership and `has` certificates.
  - No source or target theorem is used.

Audit: 26 certificates (4 principal, 22 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`.

## Formal acceptance

Coverage **194 / 357 files**, **1364 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
