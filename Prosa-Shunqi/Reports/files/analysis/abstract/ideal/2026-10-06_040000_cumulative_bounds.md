# analysis/abstract/ideal/cumulative_bounds.v — canonical translation report

First experiment timestamp: **2026-10-06 04:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/abstract/ideal/cumulative_bounds.v`; layer 25; rank 260; 12 transitive
  dependents (the ideal RTA results).
- Public declarations: **2** lemmas:
  - `cumulative_priority_inversion_is_bounded`;
  - `cumulative_interference_is_bounded_by_total_service`.
- The two section-local instances `ideal_jlfp_interference` and `ideal_jlfp_interfering_workload` are helpers.
- Dependency (accepted): `analysis/abstract/ideal/iw_instantiation.v`.

## Translation

`Prosa/Analysis/Abstract/Ideal/CumulativeBounds.lean`; it compiles with only the standard Lean axioms.

- **Binders:** follow the elaborated types. The unused sequential-tasks hypothesis is absent, as in the elaborated
  types.
- **Local instances:** the accepted `iw_instantiation` definitions of the same names, passed explicitly to the
  abstract busy interval.

Proofs use the accepted Lean results:
- `instantiated_busy_interval_equivalent_busy_interval`, to reach the classical busy interval;
- the monotonicity of the cumulative priority inversion over the interval;
- `cumulative_i_thep_eq_service_of_othep` at the ideal uniprocessor.

## Source binding

Extract mode, module `IdealCumulativeBoundsSemanticSource`:
- the two instances are byte-identical helper blocks;
- both statements are the authoritative elaborated types (`STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`).

Bindings are those of the accepted ideal `iw_instantiation` run (base closure). One recorded printer repair makes the
two local instances explicit in `definitions.busy_interval`, as in the accepted ideal `iw_instantiation` repairs.

## Validation

- **Spec** `analysis_abstract_ideal_cumulative_bounds.json`; base run `analysis_abstract_ideal_iw_instantiation`.
- **Export root:** the base root (including its definition-only ideal universe witnesses), plus the two statements.
- **Export:** 153,636 lines.

Certificate chain (51 modules), built with the same concrete-processor replay method as the accepted ideal
`iw_instantiation`:
- **The accepted replay input, replayed again at this export.** Universe-instance numbers are per export, so the 49
  replayed modules were regenerated here: 48 restricted-supply helper modules plus `PriorityInversionCorrespondence`
  (`Idl*`). **No block was dropped from any of the 49 modules.**
- **`IdlStateRel.v`:** the accepted concrete ideal processor-state relation, replayed with no block dropped.
- **`IdealCumulativeBoundsCorrespondence.v`:**
  - **Helper part:** the accepted ideal `iw_instantiation` certificate's helper part, without its statement
    correspondences.
    - Two unused helper blocks were dropped at this export: `rsi_policy_respects_sequential_rel` and
      `idl_all_jobs_from_taskset_rel`. They reference constants that only `iw_instantiation`'s own statements export.
      The header records the drop.
  - **Two statement correspondences.**
    - `icb_reorder` moves the readiness binder after the schedule.
    - Priority inversion and its bound: the accepted priority-inversion certificate.
    - Other-task higher-or-equal-priority interference: the accepted interference certificate.
    - Service of jobs: the accepted `service_of_jobs` certificate, with the replayed `another_task_hep_job` relation.
    - Arrivals and interval arithmetic: the accepted relations.

No source or target theorem is used.

Attempts:
- **Prepare attempt 1** passed.
- **Chain compile attempt 1** used a relative run path, which the compile helper resolves after changing directory.
  It found no certificate environment; its log is archived as `icb_rc_attempt1_relpath.log`.
- **Chain compile attempt 2** passed.
- **Finalization 1** was accepted.

Audit: 4 certificates, 3 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 1 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **323 / 357 files**, **2094 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
