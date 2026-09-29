# results/rta/rs/fp/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-03 03:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/rs/fp/fully_preemptive.v`; rank 354.
- Public declarations: **3**:
  - the definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - the theorem `uniprocessor_response_time_bound_fully_preemptive_fp`.
- Dependencies (all accepted): `analysis/abstract/restricted_supply/bounded_bi/fp.v`, `analysis/abstract/restricted_supply/search_space/fp.v`, `analysis/abstract/restricted_supply/task_intra_interference_bound.v`, `analysis/facts/model/task_cost.v`, `analysis/facts/preemption/rtc_threshold/preemptive.v`, `analysis/facts/preemption/task/preemptive.v`, `analysis/facts/readiness/sequential.v`.

## Translation

`Prosa/Results/Rta/Rs/Fp/FullyPreemptive.lean`.
- **The two definitions:** the busy-window recurrence (`0 < L ∧ total_hep_rbf L ≤ SBF L`) and the response-time recurrence (for every `A` in the FP search space, some `F ≤ A + R` with `task_rbf (A + 1) + total_ohep_rbf F ≤ SBF F`).
- **The theorem:** any solution `R` bounds the response times of `tsk` under fully preemptive FP scheduling with sequential readiness on a restricted-supply uniprocessor. The proof instantiates the accepted sequential abstract restricted-supply analysis. It uses the accepted bounded-busy-interval lemma for FP, the task intra-supply interference bound, the classical-to-abstract busy-SBF switch, and the accepted FP search-space inclusion.

Binders and representation:
- Binders follow the elaborated source types.
- The source's section-local instances are passed explicitly where the elaborated statements use them implicitly: `fully_preemptive_job_model`, `fully_preemptive_task_model`, `fully_preemptive_rtc_threshold`, `sequential_ready_instance arr_seq` (the local `sequential_readiness`) and the JLFP policy `FP_to_JLFP FP`.
- `ε` is `1`.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaRsFpFullyPreemptiveSemanticSource`.
- The two definitions are byte-identical computational blocks, and the theorem statement is the authoritative elaborated type (proof omitted).
- The section-local `sequential_readiness` instance is a byte-identical helper block. In the copied contexts it is a section-local `Let` declared as a local instance.
  - This required an extractor change: `#[local] Instance` context lines are now copied as `Let` + `#[local] Existing Instance`.
  - Self-referencing re-exposures, such as `rs_jlfp_interference`, are not copied.
- **Bound to accepted extracted sources**, whose `.vo` files are hash-checked against their manifests: restricted-supply instantiation, busy-SBF validity, request-bound functions, the FP search space and blocking bound, priority-driven schedules, preemption and task preemption parameters, schedulability, and the fully preemptive task model (`TaskPreemptionFullyPreemptiveSemanticSource`, copied from its accepted run).
- `model/readiness/sequential` (under its accepted Rocq 9.3 compatibility patch), `model/preemption/fully_preemptive`, `analysis/definitions/sbf/{sbf,pred}` and `util/setoid` are compiled from the pinned tree.
- The proof-only facts imports are dropped.
- Recorded printer repairs:
  - make the readiness, job-preemption and FP-policy instances implicit in the elaborated statement explicit;
  - map the own-module qualifier `fully_preemptive.X` to `X`.

The fingerprints match (3/3): the two definitions exactly modulo the own-module display qualifier, and the statement body modulo the recorded own-module qualifier repair.

## Validation

- **Spec** `results_rta_rs_fp_fully_preemptive.json`; base run `analysis_abstract_restricted_supply_bounded_bi_fp_final`.
- **Oleans:** the accepted oleans of the closure are hash-checked artifacts.
- **Export:** 145,934 lines. The export root is the accepted restricted-supply FP bounded-busy-interval root (without statements), merged with the accepted FP search-space root, plus the two definitions and the statement.
- **Chain:** the accepted restricted-supply FP bounded-busy-interval chain with the accepted FP search-space certificate.
  - `BoundedBiFpCorrespondence` and `SearchSpaceFpCorrespondence` are helper-only copies. They drop only their own files' statement correspondences, whose target statements are not part of this export.
  - The pipeline's imported-symbol preflight caught this before any chain compile (attempt 1 of the check).

Attempts:
- **Prepare attempt 1** was archived as `…_attempt1_missing_oleans`: the closure lacked the readiness/preemption-model oleans, which were then added as hash-checked artifacts.
- **Certificate compile:** fixed a binder-name clash with the section inputs (removing unused template code) and an argument order. Each re-check reused the compiled chain prefix from its checkpoints.

Certificate `RtaRsFpFullyPreemptiveCorrespondence.v`. Leading inputs:
- `task_cost`, `job_cost` and `job_arrival` pointwise;
- `max_arrivals` by the accepted `CvMaxArrivalsRel`;
- `job_task` by the accepted `AdJobTaskRel`;
- the processor state by the accepted two-sided `SvcProcessorStateRel` together with the pointwise `supply_on` relation (the accepted restricted-supply family relations).

Covered in both directions: FP policies (the local `bbf_forall_fp` of the accepted FP bounded-busy-interval certificate), supply bound functions (pointwise on Nats through their class field), task sets, arrival sequences, schedules, tasks, jobs and instants.

What is related, and how:
- **The sequential readiness model:** at each related schedule pair, from the accepted pending and `prior_jobs_complete` relations.
- **The fully preemptive job model:** pointwise.
- **Schedule validity and work conservation:** the accepted restricted-supply helper relations at that readiness model.
- **The FP policy at preemption points:** the priority-driven relation replayed at the schedule pair.
- **The accepted certificates, re-instantiated at this artifact:** the classical busy-SBF validity, the supply-bound-function predicates, the FP search space, the RBFs and the task response-time bound.

No source or target theorem is used.

Audit: 13 certificates (the two definitions, the statement and the helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

The first audit observed aliases of the already-allowed SProp `True`/`HEq` constants through `SSFP.I.*` and `SearchSpaceFpCorrespondence.I.*`. Exactly those were added to the UIP allowlist, and the finalize was re-run. The first log is kept as `.work/rtafpfp_final_attempt1_alias_allowlist.log`.

## Formal acceptance

Coverage **252 / 357 files**, **1706 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
