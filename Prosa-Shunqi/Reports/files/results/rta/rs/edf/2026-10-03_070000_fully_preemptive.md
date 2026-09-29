# results/rta/rs/edf/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-03 07:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/rs/edf/fully_preemptive.v`; rank 345.
- Public declarations: **3**:
  - the definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - the theorem `uniprocessor_response_time_bound_fully_preemptive_edf`.
- Dependencies (all accepted): `analysis/abstract/restricted_supply/bounded_bi/jlfp.v`, `analysis/abstract/restricted_supply/search_space/edf.v`, `analysis/abstract/restricted_supply/task_intra_interference_bound.v`, `analysis/facts/blocking_bound/edf.v`, `analysis/facts/model/task_cost.v`, `analysis/facts/preemption/rtc_threshold/preemptive.v`, `analysis/facts/preemption/task/preemptive.v`, `analysis/facts/priority/edf.v`, `analysis/facts/readiness/basic.v`, `analysis/facts/workload/edf_athep_bound.v`.

## Translation

`Prosa/Results/Rta/Rs/Edf/FullyPreemptive.lean`.
- **The two definitions:**
  - the busy-window recurrence: `0 < L ∧ total_rbf ts L ≤ SBF L`;
  - the response-time recurrence: for every `A` in the EDF search space (for the fully preemptive task model), some `F ≤ A + R` with `task_rbf (A + 1) + bound_on_athep_workload ts tsk A F ≤ SBF F`.
- **The theorem:** any solution `R` bounds the response times of `tsk` under fully preemptive EDF scheduling with basic readiness on a restricted-supply uniprocessor. The proof instantiates the accepted abstract restricted-supply analysis for JLFP policies. It uses the accepted JLFP bounded-busy-interval lemma, the task intra-supply interference bound, the classical-to-abstract busy-SBF switch, the accepted EDF search-space inclusion and the ATHEP workload bound. The EDF blocking bound vanishes in the fully preemptive task model; a private lemma proves this.

Binders and representation:
- Binders follow the elaborated source types.
- The fully preemptive job and task models, `basic_ready_instance` and the policy `EDF` (with job deadlines from task deadlines) are passed explicitly where the elaborated statement uses them implicitly.
- `ε` is `1`.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaRsEdfFullyPreemptiveSemanticSource`.
- The two definitions are byte-identical computational blocks, and the theorem statement is the authoritative elaborated type (proof omitted).
- **Bound to accepted extracted sources**, whose `.vo` files are hash-checked against their manifests: restricted-supply instantiation, busy-SBF validity, request-bound functions, the EDF search space and blocking bound, the ATHEP workload bound, priority-driven schedules, preemption and task preemption parameters, schedulability, and the fully preemptive task model.
- `model/preemption/fully_preemptive`, `model/priority/edf`, `analysis/definitions/sbf/{sbf,pred}` and `util/setoid` are compiled from the pinned tree.
- The proof-only facts imports are dropped.
- Recorded printer repairs:
  - make the readiness, job-preemption-model and EDF-policy instances explicit in the elaborated statement;
  - map the own-module qualifier `edf.fully_preemptive.X` to `X`.
- **Implicit-instance check:** the extracted statement was printed with `Set Printing All` and compared with the official print; they are identical up to display qualifiers.

The fingerprints match (3/3).

## Validation

- **Spec** `results_rta_rs_edf_fully_preemptive.json`; base run `analysis_abstract_restricted_supply_bounded_bi_fp_final`.
- **Oleans:** the accepted oleans of the closure are hash-checked artifacts. 50 of 53 fixture oleans were reused from the verified content-addressed cache; the three EDF-specific fixtures (first EDF response-time run) were built fresh.
- **Export:** 146,141 lines. The export root is the accepted restricted-supply JLFP bounded-busy-interval root, merged with the accepted EDF search-space root and the ATHEP workload bound root, plus the two definitions and the statement. The FP-only search-space and blocking-bound targets inherited from the FP derivation were removed.
- **Chain:** the accepted restricted-supply chain with the accepted EDF ATHEP workload bound, EDF blocking bound and EDF search-space certificates.

Attempts:
- **Prepare attempt 1** was archived as `…_attempt1_killed_fp_only_export_targets`. It was stopped because its export configuration still named FP-only targets and lacked the EDF search-space root. The prepare was rerun with the corrected configuration.
- **Finalization attempt 1** (`rtaedffp_final_attempt1_unused_fp_alias.log`): the 64-module chain prefix compiled, and the main certificate failed. It aliased `BlockingBoundFpCorrespondence`, an FP module that is not in the EDF chain and was never used. A new static check then found every `FoundationCertificates` module that a chain certificate names but its chain lacks. The same unused alias was removed from all EDF/ELF/FIFO certificates, and the check also corrected the ELF and FIFO chains before their runs.
- **Finalization attempt 2** (`rtaedffp_final_attempt2_task_model_segment_value.log`): the fully preemptive task model's maximum non-preemptive segment was related as `0`. In Prosa it is `ε = 1`, as in the accepted task-model certificate; this was corrected here and in the three sibling drafts.
- **Finalization attempt 3** (`rtaedffp_final_attempt3_alias_allowlist.log`) stopped at the assumption audit on the helper aliases `EAB`/`SSE`/`SearchSpaceEdfCorrespondence.I.{True,HEq_inst1}`, which were added to the UIP allowlist. No other assumption was reported.
- Each re-check reused the compiled chain prefix from its checkpoints (64, then all 66 modules).

Certificate `RtaRsEdfFullyPreemptiveCorrespondence.v`. Leading inputs:
- `task_cost`, `task_deadline`, `job_cost` and `job_arrival` pointwise;
- `max_arrivals` by the accepted `CvMaxArrivalsRel`;
- `job_task` by the accepted `AdJobTaskRel`;
- the processor state by the accepted two-sided `SvcProcessorStateRel` together with the pointwise `supply_on` relation.

Covered in both directions: supply bound functions, task sets, arrival sequences, schedules, tasks, jobs and instants.

What is related, and how:
- **The basic readiness model:** at each related schedule pair, from the accepted pending relation.
- **The EDF policy:** job deadlines related from arrivals and task deadlines, and the policy compared by the related `≤`.
- **The fully preemptive job and task models:** pointwise.
- **Schedule validity and work conservation:** the accepted restricted-supply helper relations at that readiness model.
- **The JLFP policy at preemption points:** replayed at the schedule pair.
- **The accepted certificates, re-instantiated at this artifact:** the busy-SBF validity for EDF, the supply-bound-function predicates, the EDF search space, the ATHEP workload bound, the RBFs and the task response-time bound.

No source or target theorem is used.

Audit: 16 certificates (the two definitions, the statement and the helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **256 / 357 files**, **1718 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
