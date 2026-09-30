# analysis/abstract/restricted_supply/task_ibf_readiness.v — canonical translation report

First experiment timestamp: **2026-10-05 22:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/abstract/restricted_supply/task_ibf_readiness.v`; layer 26; rank 277.
- Public declarations: **2**:
  - the bound `task_intra_IBF A R = athep_workload_bound A R + service_inversion_bound A +
    readiness_interference_bound A R`;
  - `instantiated_task_intra_interference_is_bounded`: it bounds the cumulative task intra-supply interference of
    the readiness-aware instantiation.
- The two section-local instances re-expose the readiness-aware instantiation; they are helpers.
- Dependencies (accepted):
  - `restricted_supply/abstract_seq_rta.v`;
  - `restricted_supply/iw_readiness.v` (accepted in this session);
  - `definitions/sbf/busy.v`, `definitions/workload/bounded.v`.

## Translation

`Prosa/Analysis/Abstract/RestrictedSupply/TaskIbfReadiness.lean`, following the accepted `TaskIntraInterferenceBound.lean`.

The lemma is proved from the accepted readiness-aware split (`cumulative_task_interference_split`):
- **Another-task hep part:** the accepted interference/workload facts and the workload bound.
- **Service-inversion part:** interval monotonicity and the readiness-aware service-inversion bound.
- **Readiness part:** the pointwise inequality `(has_supply && !ready) ≤ !ready` and the readiness-interference
  bound.

Schedule-validity consequences come from the accepted facts. The imports are only those the proof uses (the
readiness-aware iw instantiation and the bounded-workload definitions). Lean axioms: only the standard ones.

## Source binding

Extract mode, module `TaskIbfReadinessSemanticSource`:
- the two instances are byte-identical helper blocks;
- `task_intra_IBF` is a byte-identical computational block;
- the statement is the authoritative elaborated type.

Imports:
- the accepted extracted `IwReadinessSemanticSource` of the base run;
- the accepted extracted `WorkloadBoundedSemanticSource` (`.vo` copied and hash-checked);
- the recorded alias `readiness_aware` that the statement prints.

Printer repairs:
- the section-local instances are named explicitly in the three bound predicates;
- the recorded own-qualifier repair `task_ibf_readiness.task_intra_IBF=task_intra_IBF` is applied.

Fingerprints:
- **Statement:** `STATEMENT_BODY_EQUAL_MODULO_OWN_MODULE_QUALIFIER`.
- **Bound: `EXACT_HASH`.** In the official environment another `task_intra_IBF` is in scope, so `Check` prints this
  file's constant as `task_ibf_readiness.task_intra_IBF`. The probe reproduces exactly that display: at its end,
  after the statement block, a display-only alias `task_ibf_readiness` and a shadowing `task_intra_IBF` (the
  recorded display-shadow method) are declared, and the `Check` names the declaration through the alias.

## Validation

- **Spec** `analysis_abstract_restricted_supply_task_ibf_readiness.json`; base run
  `analysis_abstract_restricted_supply_iw_readiness`.
- **Export root:** the base root merged with the accepted bounded-workload root.
- **Export:** 145,730 lines.

Certificate chain:
- the accepted iw_readiness chain;
- a **helper-only copy** of the accepted `IwReadinessCorrespondence`. It was trimmed by hand; the automatic trimmer
  would have dropped the whole section. Kept blocks are byte-identical. Removed:
  - the statement correspondences, whose statements are not exported here;
  - `rsi_exists_identity` (Lean `Exists` is absent from this export) and its only user `rsi_work_conserving_related`;
- the accepted `WorkloadBoundedCorrespondence`, re-bound;
- `TaskIbfReadinessCorrespondence.v`.

Relations:
- **Input relations:** as for `task_intra_interference_bound`, plus the three bound functions, covered pointwise.
- **Readiness:** quantified before the policy, arrival sequence and schedule. The statement is first rewritten by a
  pure binder reordering (`tibfr_reorder`, no extensionality) and readiness is then covered at the schedule pair.
- **Bound predicates:** readiness-aware service inversion, readiness interference, hep workload and task intra
  interference are related by the accepted definition certificates over the accepted `rsi_interference_rel` /
  `rsi_workload_rel`.

No source or target theorem is used.

Attempts:
- **Finalization 1** stopped only at the observed `IwReadinessCorrespondence.I.{True,HEq,HEq_inst1}` helper aliases
  (log archived). They were added via `allowalias.py`.
- **Finalization 2** was accepted.

Audit: 7 certificates, 5 `CERTIFIED` and 2 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **317 / 357 files**, **1981 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
