# analysis/abstract/ideal/iw_instantiation.v — canonical translation report

First experiment timestamp: **2026-10-06 03:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/abstract/ideal/iw_instantiation.v`; layer 24; rank 259; 22 transitive
  dependents (the ideal RTA results).
- Public declarations: **20** lemmas. They cover:
  - the JLFP instantiation of interference and interfering workload for ideal uniprocessor schedules;
  - its idle-schedule and task-interference facts;
  - the cumulative splits;
  - the equivalences of the instantiated abstract quiet time, busy-interval prefix and busy interval with the
    classical notions;
  - the I/IW correctness facts, including `instantiated_busy_intervals_are_bounded`.
- The two section-local instances `ideal_jlfp_interference` and `ideal_jlfp_interfering_workload` are helpers.
- Dependencies (all accepted):
  - `analysis/abstract/IBF/task.v`, `analysis/facts/busy_interval/carry_in.v`, `analysis/facts/interference.v`;
  - `analysis/facts/model/ideal/priority_inversion.v`, `model/processor/ideal.v`.

This file was the long-standing "inst4" blocker. Every definition used by the statements is imported at the ideal
processor-model universe instance, as `_instN` copies, so the accepted generic certificates do not apply directly.
It is closed with the concrete-processor replay method already used for the overheads and exceedance models,
extended here to the ideal processor.

## Translation

`Prosa/Analysis/Abstract/Ideal/IwInstantiation.lean`, unchanged from its earlier translation; it compiles with only
the standard Lean axioms.

- **Binders:** follow the elaborated types.
- **Local instances:** the definitions of the same names, passed explicitly.
- **Busy-interval notions:** the classical and abstract ones are distinguished by namespace.

## Source binding

Extract mode, module `IdealIwInstantiationSemanticSource`:
- the two instances are byte-identical helper blocks;
- the 20 statements are the authoritative elaborated types. All 20 fingerprints are
  `STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`.

Bindings, from the base closure (the accepted restricted-supply `iw_instantiation` run):
- IBF/task, the interference definitions, the classical busy intervals and priority inversion: the accepted extracted
  sources;
- `work_conserving` and `work_bearing_readiness`: the accepted artifacts.

`model/processor/ideal` is the pinned source under its accepted Rocq 9.3 compatibility patch.

Recorded printer repairs make the two local instances explicit, adapted from the accepted restricted-supply repairs.
They cover `task_interference`, `cumul_task_interference`, `~ interference` and `busy_intervals_are_bounded_by`.

## Validation

- **Spec** `analysis_abstract_ideal_iw_instantiation.json`; base run `analysis_abstract_restricted_supply_iw_instantiation`.
- **Export root:** the base root merged with:
  - the accepted ideal-schedule root, including its kernel-checked ideal-state closed forms;
  - the validation-only ideal universe witnesses of `IdealInstWitnessComputationInterface`. These are 154 `w_*`
    definitions, each applying one generic processor-state-dependent constant of the base root at the ideal
    processor. No statement or equation is added.
- **Export:** 154,793 lines.

Certificate chain (51 modules):
- **The accepted restricted-supply chain, replayed.** 48 generic helper modules, plus the accepted
  `PriorityInversionCorrespondence`, are replayed at the ideal instance of this export by the processor-model replay
  tool (`Idl*` modules). Each imported constant with a universe-specialised copy is renamed to it; the core-list
  machinery moves to the core-level list type. **No block was dropped from any of the 49 modules.**
- **`IdlStateRel.v` (new): the concrete ideal processor-state relation.**
  - States are related by the Option map, and the core is the unit core.
  - The Lean core enumeration is shown to be the singleton list from the accepted `coreEnumeration`
    duplicate-freedom and completeness interface theorems, by case analysis on the Lean list.
  - `scheduled_on`/`service_on` are related per core, and the supply is unit.
- **`IdealIwInstantiationCorrespondence.v`: the main certificate.**
  - Its helper part is the accepted restricted-supply certificate's, with the generic processor-state relation
    instantiated to the ideal one. The restricted-supply-only helper `rsi_unit_supply_rel` is not generated.
  - The two instances are related field by field:
    - priority inversion by the accepted priority-inversion certificate;
    - the higher-or-equal-priority interference / interfering workload by the accepted interference certificate.
  - The ideal idle predicate and `all_jobs_from_taskset` are related by unfolding.
  - The IBF/task, curves, request-bound-function, abstract-definition and busy-interval notions use the accepted
    certificates.

No source or target theorem is used.

Attempts:
- **Prepare attempt 1** was stopped and archived as `_attempt1_import_hang`. The witness fixture also contained
  witnesses for the restricted-supply theorems, which pulled `Nat.Internal.Linear` proofs into the export (448,854
  lines), so the Rocq import hung. Those 16 theorem witnesses were removed; only definitions are witnessed.
- **Prepare attempt 2** passed.
- **Finalization 1** stopped at the observed helper-alias SProp truth constants.
  - The `X.I.{True,HEq,HEq_inst1}` aliases were added via `allowalias.py`.
  - Four further entries were added: `IdlArrivalsSeqBaseAdapter.ArTrue`, `IdlJitterSvcBaseAdapter.SvcTrue`,
    `IdlServiceBaseAdapter.SvcTrue` and `IdlServiceScheduleOperations.SvcSourceTrue`. These are the exact
    replay-renamed counterparts of entries already in the accepted allowlist
    (`ArrivalsSeqBaseAdapter.ArTrue`, `JitterSvcBaseAdapter.SvcTrue`, `ServiceBaseAdapter.SvcTrue`,
    `ServiceScheduleOperations.SvcSourceTrue`): the same `Inductive … : SProp` declarations under the replayed
    module names.
- **Finalization 2** was accepted, but it was published with stale chain metadata: `previous_status` still pointed
  to `wc_correctness` (320/2077). The README cross-check rejected it.
  - The published status, manifest and publication destination were moved into
    `publish_attempt1_stale_chain` of the run.
  - The spec was chained to `results_optimality_edf` (321/2072).
  - The same certified artifacts were republished (finalizations 3–5; 3 and 4 were refused by the pipeline's
    publication guards until the stale files were moved).

Audit: 22 certificates, all `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **322 / 357 files**, **2092 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
