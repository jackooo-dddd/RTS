# results/rta/rs/elf/floating_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-10-03 16:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/rs/elf/floating_nonpreemptive.v`; rank 347.
- Public declarations: **3**:
  - the definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - the theorem `uniprocessor_response_time_bound_floating_elf`.
- Dependencies (all accepted): `analysis/abstract/restricted_supply/bounded_bi/elf.v`, `analysis/abstract/restricted_supply/search_space/elf.v`, `analysis/abstract/restricted_supply/task_intra_interference_bound.v`, `analysis/definitions/sbf/busy.v`, `analysis/facts/blocking_bound/elf.v`, `analysis/facts/model/task_cost.v`, `analysis/facts/preemption/rtc_threshold/floating.v`, `analysis/facts/priority/elf.v`, `analysis/facts/readiness/basic.v`, `analysis/facts/workload/elf_athep_bound.v`.

## Translation

`Prosa/Results/Rta/Rs/Elf/FloatingNonpreemptive.lean`.
- **The two definitions:**
  - the busy-window recurrence: `0 < L ∧ ∀ A, blocking_bound ts tsk A + total_hep_rbf L ≤ SBF L` (with respect to the FP policy `FP` that ELF refines);
  - the response-time recurrence: for every `A` in the ELF search space, some `F ≤ A + R` with `blocking_bound ts tsk A + task_rbf (A + 1) + bound_on_athep_workload ts tsk A F ≤ SBF F`.
- **The theorem:** any solution `R` bounds the response times of `tsk` under ELF scheduling with floating non-preemptive regions (limited-preemptive job model, a task model bounding the non-preemptive segments, a schedule respecting the preemption model; EDF within priority levels of `FP`, with task priority points) with basic readiness on a restricted-supply uniprocessor. The proof instantiates the accepted abstract restricted-supply analysis for JLFP policies. It uses the accepted ELF bounded-busy-interval lemma, the task intra-supply interference bound, the classical-to-abstract busy-SBF switch, the accepted ELF search-space inclusion and the ELF ATHEP workload bound.

Binders and representation:
- Binders follow the elaborated source types.
- The limited-preemptive job model, `floating_preemptive_rtc_threshold`, `basic_ready_instance` and the policy `ELF FP` are passed explicitly where the elaborated statement uses them implicitly.
- `ε` is `1`.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaRsElfFloatingNonpreemptiveSemanticSource`.
- The two definitions are byte-identical computational blocks, and the theorem statement is the authoritative elaborated type (proof omitted).
- **Bound to accepted extracted sources**, whose `.vo` files are hash-checked against their manifests: restricted-supply instantiation, busy-SBF validity, request-bound functions, the ELF search space and blocking bound, the ELF ATHEP workload bound (with the EDF ATHEP bound it builds on), priority-driven schedules, preemption and task preemption parameters, schedulability, and the limited-preemptive job model, the floating non-preemptive task model and the limited-preemptive schedule predicate (`LimitedPreemptiveSemanticSource`, `TaskFloatingNonpreemptiveSemanticSource`, `ScheduleLimitedPreemptiveSemanticSource`, copied from their accepted runs).
- `analysis/definitions/sbf/{sbf,pred}` and `util/setoid` are compiled from the pinned tree; `util/int` and `model/priority/{gel,elf}` come from the base source tree.
- The proof-only facts imports are dropped.
- Recorded printer repairs:
  - make the readiness, job-preemption-model and ELF-policy instances explicit in the elaborated statement;
  - map the own-module qualifier `elf.floating_nonpreemptive.X` to `X`.
- **Implicit-instance check:** the extracted statement was printed with `Set Printing All` and compared with the official print; they are identical up to display qualifiers.

The fingerprints match (3/3).

## Validation

- **Spec** `results_rta_rs_elf_floating_nonpreemptive.json`; base run `analysis_abstract_restricted_supply_bounded_bi_fp_final`.
- **Oleans:** the accepted oleans of the closure are hash-checked artifacts. 59 of 60 fixture oleans were reused from the verified content-addressed cache.
- **Export:** 184,185 lines. The export root is the accepted restricted-supply JLFP bounded-busy-interval root, merged with the accepted ELF search-space root, plus the two definitions and the statement.
- **Chain:** the accepted restricted-supply chain with the accepted GEL/ELF priority helpers, the EDF and ELF ATHEP workload bounds, the ELF blocking bound and the ELF search-space certificates, the accepted limited-preemptive job and schedule model certificates and the accepted floating non-preemptive task model certificate.
  - The static chain-reference check restored the EDF ATHEP workload bound (artifact, fixture and chain module) before the first prepare. The ELF certificates build on it, and the derivation from the EDF response-time specification had dropped it.

Attempts:
- **Finalization:** accepted on the first attempt. The chain compiled on the first check (76 modules), and the recheck after pruning reused all 76 from their checkpoints. The helper aliases this run observed were already in the UIP allowlist. This file's check and publication ran under the pipeline revision whose imported-symbol preflight also covers the imported type audit.

Certificate `RtaRsElfFloatingNonpreemptiveCorrespondence.v`. Leading inputs:
- `task_cost`, `job_cost` and `job_arrival` pointwise;
- task priority points by the accepted `GelPriorityPointRel`;
- `max_arrivals` by the accepted `CvMaxArrivalsRel`;
- task maximum non-preemptive segments by the accepted `TppMaxSegmentRel`;
- job preemption points by the accepted `LpJobPreemptionPointsRel`;
- `job_task` by the accepted `AdJobTaskRel`;
- the processor state by the accepted two-sided `SvcProcessorStateRel` together with the pointwise `supply_on` relation.

Covered in both directions: FP policies, supply bound functions, task sets, arrival sequences, schedules, tasks, jobs and instants.

What is related, and how:
- **The basic readiness model:** at each related schedule pair, from the accepted pending relation.
- **The ELF policy:** the accepted `ELF_correspondence` at the related FP policy and priority points, as in the accepted ELF bounded-busy-interval certificate.
- **The limited-preemptive job model:** from the accepted limited-preemptive model certificate at the related preemption points.
- **`valid_model_with_floating_nonpreemptive_regions`:** the accepted floating non-preemptive model certificate.
- **The schedule's preemption model:** the accepted limited-preemptive schedule certificate.
- **The ELF blocking bound:** the accepted certificate.
- **Schedule validity and work conservation:** the accepted restricted-supply helper relations at that readiness model.
- **The JLFP policy at preemption points:** replayed at the schedule pair.
- **The accepted certificates, re-instantiated at this artifact:** the busy-SBF validity for ELF, the supply-bound-function predicates, the ELF search space, the ATHEP workload bound, the RBFs and the task response-time bound.

No source or target theorem is used.

Audit: 13 certificates (the two definitions, the statement and the helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **265 / 357 files**, **1745 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
