# results/rta/rs/edf/floating_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-10-03 10:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/rs/edf/floating_nonpreemptive.v`; rank 343.
- Public declarations: **3**:
  - the definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - the theorem `uniprocessor_response_time_bound_floating_edf`.
- Dependencies (all accepted): `analysis/abstract/restricted_supply/bounded_bi/edf.v`, `analysis/abstract/restricted_supply/search_space/edf.v`, `analysis/abstract/restricted_supply/task_intra_interference_bound.v`, `analysis/definitions/sbf/busy.v`, `analysis/facts/blocking_bound/edf.v`, `analysis/facts/model/task_cost.v`, `analysis/facts/preemption/rtc_threshold/floating.v`, `analysis/facts/priority/edf.v`, `analysis/facts/readiness/basic.v`, `analysis/facts/workload/edf_athep_bound.v`.

## Translation

`Prosa/Results/Rta/Rs/Edf/FloatingNonpreemptive.lean`.
- **The two definitions:**
  - the busy-window recurrence: `0 < L ∧ total_rbf ts L ≤ SBF L ∧ longest_busy_interval_with_pi ts tsk ≤ SBF L`;
  - the response-time recurrence: for every `A` in the EDF search space, some `F ≤ A + R` with `blocking_bound ts tsk A + task_rbf (A + 1) + bound_on_athep_workload ts tsk A F ≤ SBF F`.
- **The theorem:** any solution `R` bounds the response times of `tsk` under EDF scheduling with floating non-preemptive regions (limited-preemptive job model, a task model bounding the non-preemptive segments, a schedule respecting the preemption model) with basic readiness on a restricted-supply uniprocessor. The proof instantiates the accepted abstract restricted-supply analysis for JLFP policies. It uses the accepted EDF bounded-busy-interval lemma (with the priority-inversion bound), the task intra-supply interference bound, the classical-to-abstract busy-SBF switch, the accepted EDF search-space inclusion and the ATHEP workload bound.

Binders and representation:
- Binders follow the elaborated source types.
- The limited-preemptive job model, `floating_preemptive_rtc_threshold`, `basic_ready_instance` and the policy `EDF` (with job deadlines from task deadlines) are passed explicitly where the elaborated statement uses them implicitly.
- `ε` is `1`.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaRsEdfFloatingNonpreemptiveSemanticSource`.
- The two definitions are byte-identical computational blocks, and the theorem statement is the authoritative elaborated type (proof omitted).
- **Bound to accepted extracted sources**, whose `.vo` files are hash-checked against their manifests: restricted-supply instantiation, busy-SBF validity, request-bound functions, the EDF search space and blocking bound, the ATHEP workload bound, the EDF priority-inversion bound, priority-driven schedules, preemption and task preemption parameters, schedulability, and the limited-preemptive job model, the floating non-preemptive task model and the limited-preemptive schedule predicate (`LimitedPreemptiveSemanticSource`, `TaskFloatingNonpreemptiveSemanticSource`, `ScheduleLimitedPreemptiveSemanticSource`, copied from their accepted runs).
- `model/priority/edf`, `analysis/definitions/sbf/{sbf,pred}` and `util/setoid` are compiled from the pinned tree.
- The proof-only facts imports are dropped.
- Recorded printer repairs:
  - make the readiness, job-preemption-model and EDF-policy instances explicit in the elaborated statement;
  - map the own-module qualifier `edf.floating_nonpreemptive.X` to `X`.
- **Implicit-instance check:** the extracted statement was printed with `Set Printing All` and compared with the official print; they are identical up to display qualifiers.

The fingerprints match (3/3).

## Validation

- **Spec** `results_rta_rs_edf_floating_nonpreemptive.json`; base run `analysis_abstract_restricted_supply_bounded_bi_fp_final`.
- **Oleans:** the accepted oleans of the closure are hash-checked artifacts. 53 of 54 fixture oleans were reused from the verified content-addressed cache.
- **Export:** 146,637 lines. The export root is the accepted restricted-supply JLFP bounded-busy-interval root, merged with the accepted EDF search-space root, the ATHEP workload bound root, the accepted EDF priority-inversion-bound root (`longest_busy_interval_with_pi`), the accepted limited-preemptive job and schedule model roots and the accepted floating non-preemptive task model root, plus the two definitions and the statement.
- **Chain:** the accepted restricted-supply chain with the accepted EDF ATHEP workload bound, EDF blocking bound, EDF search-space, EDF priority-inversion-bound, limited-preemptive and floating non-preemptive model certificates.

Attempts:
- **Prepare:** the export configuration was corrected (FP-only targets removed, the EDF search-space root merged) before this file's first prepare.
- **Before the first check**, the fixes found on earlier files were already applied (the unused FP alias, the `lp_limited_preemptive_job_model_related` argument order): the unused FP alias was removed, and the static chain-reference and lemma-signature checks passed.
- **Finalization:** accepted on the first attempt. The chain compiled on the first check (70 modules), and the recheck after pruning reused all 70 from their checkpoints. The helper aliases this run observed were already in the UIP allowlist from the earlier EDF and floating non-preemptive files.

Certificate `RtaRsEdfFloatingNonpreemptiveCorrespondence.v`. Leading inputs:
- `task_cost`, `task_deadline`, `job_cost` and `job_arrival` pointwise;
- `max_arrivals` by the accepted `CvMaxArrivalsRel`;
- task maximum non-preemptive segments by the accepted `TppMaxSegmentRel`;
- job preemption points by the accepted `LpJobPreemptionPointsRel`;
- `job_task` by the accepted `AdJobTaskRel`;
- the processor state by the accepted two-sided `SvcProcessorStateRel` together with the pointwise `supply_on` relation.

Covered in both directions: supply bound functions, task sets, arrival sequences, schedules, tasks, jobs and instants.

What is related, and how:
- **The basic readiness model:** at each related schedule pair, from the accepted pending relation.
- **The EDF policy:** job deadlines related from arrivals and task deadlines, and the policy compared by the related `≤`.
- **The limited-preemptive job model:** from the accepted limited-preemptive model certificate at the related preemption points.
- **`valid_model_with_floating_nonpreemptive_regions`:** the accepted floating non-preemptive model certificate.
- **The schedule's preemption model:** the accepted limited-preemptive schedule certificate.
- **The EDF blocking bound and `longest_busy_interval_with_pi`:** the accepted certificates.
- **Schedule validity and work conservation:** the accepted restricted-supply helper relations at that readiness model.
- **The JLFP policy at preemption points:** replayed at the schedule pair.
- **The accepted certificates, re-instantiated at this artifact:** the busy-SBF validity for EDF, the supply-bound-function predicates, the EDF search space, the ATHEP workload bound, the RBFs and the task response-time bound.

No source or target theorem is used.

Audit: 15 certificates (the two definitions, the statement and the helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **259 / 357 files**, **1727 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
