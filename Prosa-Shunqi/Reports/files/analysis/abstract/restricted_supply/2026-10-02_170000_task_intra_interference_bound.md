# analysis/abstract/restricted_supply/task_intra_interference_bound.v — canonical translation report

First experiment timestamp: **2026-10-02 17:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/abstract/restricted_supply/task_intra_interference_bound.v`; rank 288.
- Public declarations: **2**:
  - the definition `task_intra_IBF`;
  - the lemma `instantiated_task_intra_interference_is_bounded`.
- Dependencies (all accepted): `analysis/abstract/restricted_supply/abstract_seq_rta.v`, `analysis/abstract/restricted_supply/iw_instantiation.v`, `analysis/definitions/sbf/busy.v`, `analysis/definitions/workload/bounded.v`.

## Translation

`Prosa/Analysis/Abstract/RestrictedSupply/TaskIntraInterferenceBound.lean`.
- `task_intra_IBF` is the sum of the service-inversion bound and the bound on the higher-or-equal-priority workload of other tasks.
- Binders follow the elaborated source types. The unused sequential-tasks hypothesis is absent, as in the elaborated type. Instance inputs quantified after a hypothesis are `∀ [..]` binders at that position.
- The source's section-local instances `rs_jlfp_interference` and `rs_jlfp_interfering_workload` are the accepted definitions of the same names, passed explicitly where the elaborated statement uses them implicitly.
- The service-inversion bound is the classical one of `analysis/definitions/service_inversion/busy_prefix.v`: the name the elaborated type resolves to, checked in the official environment.

The proof follows the source:
- the accepted split of the task interference;
- the service-inversion bound over the enclosing busy-interval prefix (widened from `[t1, t1 + Δ)`);
- the higher-or-equal-priority interference of other tasks as their service, bounded by their workload and then by the workload bound.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `TaskIntraInterferenceBoundSemanticSource`.
- The two section-local instances are byte-identical helper blocks.
- `task_intra_IBF` is a byte-identical computational block.
- The lemma statement is the authoritative elaborated type.
- `iw_instantiation`, `service_inversion/busy_prefix` and `workload/bounded` are bound to their accepted extracted sources. Their `.vo` files are copied from the accepted runs and hash-checked against their manifests.
- The proof-only `abstract_seq_rta` and `sbf/busy` imports are dropped.
- The two instances implicit in the elaborated statement are made explicit by a recorded printer repair. The statement prints back to the evidence text.

The fingerprints match (2/2).

## Validation

- **Spec** `analysis_abstract_restricted_supply_task_intra_interference_bound.json`; base run `analysis_abstract_restricted_supply_iw_instantiation_final`.
- **Oleans:** the accepted oleans of the closure are hash-checked artifacts.
- **Export:** 144,896 lines. The export root is the accepted restricted-supply instantiation root (without statements) merged with the accepted bounded-workload root, plus the definition and the statement.
- **Chain:** the accepted restricted-supply instantiation chain, with the accepted bounded-workload and classical service-inversion-bound certificates. `RsIwHelpers.v` is its helper-only copy:
  - truncated before its statement correspondences;
  - also without the helper `rsi_policy_respects_sequential_rel`, whose target constant `policy_respects_sequential_tasks` is not part of this export.

Certificate `TaskIntraInterferenceBoundCorrespondence.v`.

**`task_intra_IBF`:** the extracted definition against the compiled Lean definition. Its two bound functions are related pointwise on related Nats.

**The lemma.** Leading inputs:
- `job_cost` and `job_arrival` pointwise;
- `job_task` by the accepted `AdJobTaskRel`;
- the processor state by the accepted two-sided `SvcProcessorStateRel` with the pointwise `supply_on` relation.

JLFP policies, arrival sequences, schedules, tasks and the two bound functions are covered in both directions.

What is related, and how:
- **The section-local instances:** the accepted `rsi_interference_rel`/`rsi_workload_rel`.
- **The classical service-inversion bound, the higher-or-equal-priority workload bound and the task intra-supply interference bound:** the accepted definition certificates, re-instantiated at this artifact.

No source or target theorem is used.

Audit: 2 principal certificates plus the helper lemmas, all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. The audit observed aliases of the already-allowed SProp `True`/`HEq` constants through `ServiceInversionBusyPrefixCorrespondence.I.*` and the certificate's module aliases `SIBP.I.*` and `WLB.I.*`; I added exactly those to the UIP allowlist.

## Formal acceptance

Coverage **242 / 357 files**, **1687 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
