# results/rta/rs/elf/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-03 13:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/rs/elf/fully_preemptive.v`; rank 349.
- Public declarations: **3**:
  - the definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - the theorem `uniprocessor_response_time_bound_fully_preemptive_elf`.
- Dependencies (all accepted): `analysis/abstract/restricted_supply/bounded_bi/elf.v`, `analysis/abstract/restricted_supply/search_space/elf.v`, `analysis/abstract/restricted_supply/task_intra_interference_bound.v`, `analysis/facts/blocking_bound/elf.v`, `analysis/facts/model/task_cost.v`, `analysis/facts/preemption/rtc_threshold/preemptive.v`, `analysis/facts/preemption/task/preemptive.v`, `analysis/facts/priority/elf.v`, `analysis/facts/readiness/basic.v`, `analysis/facts/workload/elf_athep_bound.v`.

## Translation

`Prosa/Results/Rta/Rs/Elf/FullyPreemptive.lean`.
- **The two definitions:**
  - the busy-window recurrence: `0 < L ∧ total_hep_rbf L ≤ SBF L` (with respect to the FP policy `FP` that ELF refines);
  - the response-time recurrence: for every `A` in the ELF search space (for the fully preemptive task model), some `F ≤ A + R` with `task_rbf (A + 1) + bound_on_athep_workload ts tsk A F ≤ SBF F`.
- **The theorem:** any solution `R` bounds the response times of `tsk` under fully preemptive ELF scheduling (EDF within priority levels of `FP`, with task priority points) with basic readiness on a restricted-supply uniprocessor. The proof instantiates the accepted abstract restricted-supply analysis for JLFP policies. It uses the accepted ELF bounded-busy-interval lemma, the task intra-supply interference bound, the classical-to-abstract busy-SBF switch, the accepted ELF search-space inclusion and the ELF ATHEP workload bound. The ELF blocking bound vanishes in the fully preemptive task model; a private lemma proves this.

Binders and representation:
- Binders follow the elaborated source types.
- The fully preemptive job and task models, `basic_ready_instance` and the policy `ELF FP` are passed explicitly where the elaborated statement uses them implicitly.
- `ε` is `1`.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaRsElfFullyPreemptiveSemanticSource`.
- The two definitions are byte-identical computational blocks, and the theorem statement is the authoritative elaborated type (proof omitted).
- **Bound to accepted extracted sources**, whose `.vo` files are hash-checked against their manifests: restricted-supply instantiation, busy-SBF validity, request-bound functions, the ELF search space and blocking bound, the ELF ATHEP workload bound (with the EDF ATHEP bound it builds on), priority-driven schedules, preemption and task preemption parameters, schedulability, and the fully preemptive task model.
- `model/preemption/fully_preemptive`, `analysis/definitions/sbf/{sbf,pred}` and `util/setoid` are compiled from the pinned tree; `util/int` and `model/priority/{gel,elf}` come from the base source tree.
- The proof-only facts imports are dropped.
- Recorded printer repairs:
  - make the readiness, job-preemption-model and ELF-policy instances explicit in the elaborated statement;
  - map the own-module qualifier `elf.fully_preemptive.X` to `X`.
- **Implicit-instance check:** the extracted statement was printed with `Set Printing All` and compared with the official print; they are identical up to display qualifiers.

The fingerprints match (3/3).

## Validation

- **Spec** `results_rta_rs_elf_fully_preemptive.json`; base run `analysis_abstract_restricted_supply_bounded_bi_fp_final`.
- **Oleans:** the accepted oleans of the closure are hash-checked artifacts. 52 of 60 fixture oleans were reused from the verified content-addressed cache; the eight ELF-specific fixtures (first ELF response-time run) were built fresh.
- **Export:** 183,782 lines. The export root is the accepted restricted-supply JLFP bounded-busy-interval root, merged with the accepted ELF search-space root, plus the two definitions and the statement.
- **Chain:** the accepted restricted-supply chain with the accepted GEL/ELF priority helpers, the EDF and ELF ATHEP workload bounds, the ELF blocking bound and the ELF search-space certificates.
  - The static chain-reference check restored the EDF ATHEP workload bound (artifact, fixture and chain module) before the first prepare. The ELF certificates build on it, and the derivation from the EDF response-time specification had dropped it.

Attempts:
- **Finalization attempt 1** (`rtaelffp_final_attempt1_alias_allowlist.log`): the chain compiled on the first check (73 modules). The fixes found on the EDF files (the unused FP alias, the `ε = 1` task-model segment) were already applied. Finalization stopped at the assumption audit on the helper aliases `EABE`/`SSEL`/`SearchSpaceElfCorrespondence.I.{True,HEq_inst1}`, which were added to the UIP allowlist; no other assumption was reported.
- **Finalization attempt 2** was accepted. Each re-check reused all 73 modules from their checkpoints.

Certificate `RtaRsElfFullyPreemptiveCorrespondence.v`. Leading inputs:
- `task_cost`, `job_cost` and `job_arrival` pointwise;
- task priority points by the accepted `GelPriorityPointRel`;
- `max_arrivals` by the accepted `CvMaxArrivalsRel`;
- `job_task` by the accepted `AdJobTaskRel`;
- the processor state by the accepted two-sided `SvcProcessorStateRel` together with the pointwise `supply_on` relation.

Covered in both directions: FP policies, supply bound functions, task sets, arrival sequences, schedules, tasks, jobs and instants.

What is related, and how:
- **The basic readiness model:** at each related schedule pair, from the accepted pending relation.
- **The ELF policy:** the accepted `ELF_correspondence` at the related FP policy and priority points, as in the accepted ELF bounded-busy-interval certificate.
- **The fully preemptive job and task models:** pointwise; the task model's maximum non-preemptive segment is `ε = 1` on both sides.
- **Schedule validity and work conservation:** the accepted restricted-supply helper relations at that readiness model.
- **The JLFP policy at preemption points:** replayed at the schedule pair.
- **The accepted certificates, re-instantiated at this artifact:** the busy-SBF validity for ELF, the supply-bound-function predicates, the ELF search space, the ATHEP workload bound, the RBFs and the task response-time bound.

No source or target theorem is used.

Audit: 14 certificates (the two definitions, the statement and the helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **262 / 357 files**, **1736 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
