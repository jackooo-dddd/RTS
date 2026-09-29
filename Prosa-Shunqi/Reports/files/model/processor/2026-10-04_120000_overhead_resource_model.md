# model/processor/overhead_resource_model.v — canonical translation report

First experiment timestamp: **2026-10-04 12:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `model/processor/overhead_resource_model.v`; rank 264.
- Public declarations: **10** definitions:
  - `time_spent_in_dispatch`, `time_spent_in_context_switch` and `time_spent_in_CRPD`;
  - `time_spent_in_dispatch_is_bounded_by`, `time_spent_in_context_switch_is_bounded_by` and `time_spent_in_CRPD_is_bounded_by`;
  - `dispatch_precedes_context_switch`, `context_switch_precedes_progress` and `context_switch_precedes_CRPD`;
  - `overhead_resource_model`.
- Dependencies (all accepted): `model/processor/overheads.v`, `analysis/definitions/overheads/schedule_change.v`, `analysis/facts/model/overheads/schedule_change.v`.

## Translation

`Prosa/Model/Processor/OverheadResourceModel.lean`. It defines the overhead resource model of the overheads processor:
- **Overhead time:** the time a job (or the idle thread, `none`) spends in each kind of overhead over `[t1, t2)`. Each is an interval sum of the indicator "`oj` is scheduled and the instant is an overhead of that kind".
- **Bounds:** the bounds on these times over every stretch where `scheduled_job_invariant` holds.
- **Ordering:** within such a stretch, no context switch up to a dispatch instant, and no progress or CRPD up to a context-switch instant.
- **The model:** the conjunction of the six properties.

Binders follow the elaborated source types (`t1 t2 oj` for the bounds, `oj t1 t2` for the orderings). Boolean components use the house conventions: `~~ b` as `(!b) = true`, and `a <= t < b` as a decided conjunction. The interval sums are `Finset.Ico` sums of `Bool.toNat`.

## Source binding

Extract mode, module `OverheadResourceModelSemanticSource`.
- The ten definitions are byte-identical to the official source.
- `model/processor/overheads` and `analysis/definitions/overheads/schedule_change` are compiled from the pinned tree (as accepted).
- The facts import (proof-only) is dropped.
- The section variables are bound locally: `local_bindings`, where each definition takes the schedule `sched` explicitly.

The fingerprints match (10/10).

## Validation

- **Spec** `model_processor_overhead_resource_model.json`; base run `analysis_facts_model_overheads_schedule_change_final`.
- **Oleans:** hash-checked artifacts; 29 of 29 fixture oleans reused from the verified cache.
- **Export:** 150,671 lines; Rocq import in 48 s. The export root merges the accepted overheads schedule-change facts root with the accepted overheads processor-model root, plus the ten definitions.

**Body projections.** The three interval sums are exported through list-fold projections of the root fixture, `List.foldr Nat.add 0 ((List.range' t1 (t2 - t1) 1).map f)`. Each has a kernel-checked guard `@time_spent_in_X = @timeSpentInXProjection := rfl`, and the guards are listed in `normalization.body_projections` and in `kernel_guard_artifacts`. Without them, the raw `Finset.Ico` bodies pull the Finset/LocallyFiniteOrder internals into the export.

Attempts:
- **Prepare attempt 1** was archived as `…_attempt1_root_missing_base_import`. The root fixture did not import the base root, so a guard was not recognised as a theorem. Fixed in the root and in the fixture generator.
- **Prepare attempt 2** was archived as `…_attempt2_finset_import_blowup`. Without body projections, the export grew by about 58k lines, and the Rocq import ran more than 2.5 h before it was stopped.
- **Prepare attempt 3** was archived as `…_attempt3_total_time_finset_import`. The merged `total_time_in_*` definitions of the accepted overheads processor-model fixture still carried raw Finset bodies; they are not used here and were removed from the targets.
- **Prepare attempt 4** passed.
- **Finalization attempt 1** failed the assumption audit (log archived as `orm_finalize_attempt1_sctrue_audit.log`). The truth lemmas of the schedule-change and overheads adapters introduce their local SProp constants `ScTrue` and `OvhTrue`, which are not in the allowlist. The certificate was changed to transport truth through the already allowlisted arrivals adapter: the three boolean relations are the same map, and the bridges `orm_sc_ar` and `orm_ovh_ar` prove it by case analysis. The allowlist was not extended.
- **Finalization attempt 2** was accepted.

Chain (13 modules): the arrivals base adapter and operations, the six schedule-change modules, and the four overheads modules, re-bound to this export, followed by `OverheadResourceModelCorrespondence.v`. The overheads processor-model helper copy drops these parts, as recorded in its header:
- its `Print Assumptions` commands;
- its `total_time_in_*` interval-count section (those definitions are not part of this export);
- its `ConcreteOverheads` section. This section holds the processor-state instance fields; in this export the processor-state instance is a universe-specialised copy, and nothing here uses that section.

Certificate `OverheadResourceModelCorrespondence.v`. Leading input: the job type.

Related and covered in both directions:
- overheads schedules, by the accepted pointwise relation `OvhScheduleRel`; each related pair is also related by the accepted schedule-change relation `ScScheduleRel`, since both state maps are constructor-wise (`orm_sc_sched`);
- option jobs by `ScOptionRel` (the local cover `orm_forall_option`);
- instants and bounds by `SubNatRel`.

What each definition is proved from:
- **The sums:** the accepted interval-sum relation, with `scheduled_job` and the `is_*` observations from the accepted certificates.
- **The bounds and orderings:** the forall/implication/conjunction relations and the accepted `scheduled_job_invariant` certificate. Negation uses the local `orm_negb_related`.

No source or target theorem is used.

Audit: 18 certificates (the ten definitions and eight helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **285 / 357 files**, **1818 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
