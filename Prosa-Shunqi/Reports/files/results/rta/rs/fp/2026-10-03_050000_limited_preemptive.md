# results/rta/rs/fp/limited_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-03 05:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/rs/fp/limited_preemptive.v`; rank 355.
- Public declarations: **3**:
  - the definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - the theorem `uniprocessor_response_time_bound_limited_fp`.
- Dependencies (all accepted): `analysis/abstract/restricted_supply/bounded_bi/fp.v`, `analysis/abstract/restricted_supply/search_space/fp.v`, `analysis/abstract/restricted_supply/task_intra_interference_bound.v`, `analysis/facts/model/task_cost.v`, `analysis/facts/preemption/rtc_threshold/limited.v`, `analysis/facts/readiness/sequential.v`.

## Translation

`Prosa/Results/Rta/Rs/Fp/LimitedPreemptive.lean`.
- **The two definitions:**
  - the busy-window recurrence: `0 < L ∧ blocking_bound ts tsk + total_hep_rbf L ≤ SBF L`;
  - the response-time recurrence: for every `A` in the FP search space, some `F ≤ A + R` with `blocking_bound ts tsk + (task_rbf (A + 1) - (task_last_nonpr_segment tsk - 1)) + total_ohep_rbf F ≤ SBF F` and `SBF F + (task_last_nonpr_segment tsk - 1) ≤ SBF (A + R)`.
- **The theorem:** any solution `R` bounds the response times of `tsk` under FP scheduling with fixed preemption points (limited-preemptive job and task models, a schedule respecting the preemption model), with sequential readiness on a restricted-supply uniprocessor. The proof instantiates the accepted sequential abstract restricted-supply analysis. It uses the accepted bounded-busy-interval lemma for FP, the task intra-supply interference bound, the classical-to-abstract busy-SBF switch, and the accepted FP search-space inclusion.

Binders and representation:
- Binders follow the elaborated source types.
- The section-local instances are passed explicitly where the elaborated statements use them implicitly: `limited_preemptive_job_model`, `limited_preemptions_rtc_threshold`, `sequential_ready_instance arr_seq` (the local `sequential_readiness`) and the JLFP policy `FP_to_JLFP FP`.
- `ε` is `1`.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaRsFpLimitedPreemptiveSemanticSource`.
- The two definitions are byte-identical computational blocks, and the theorem statement is the authoritative elaborated type (proof omitted).
- The section-local `sequential_readiness` instance is a byte-identical helper block, copied into the contexts as a `Let` with a local `Existing Instance`.
- **Bound to accepted extracted sources**, whose `.vo` files are hash-checked against their manifests: restricted-supply instantiation, busy-SBF validity, request-bound functions, the FP search space, priority-driven schedules, preemption and task preemption parameters, schedulability, and the three limited-preemptive models (`LimitedPreemptiveSemanticSource`, `TaskLimitedPreemptiveSemanticSource`, `ScheduleLimitedPreemptiveSemanticSource`, copied from their accepted runs).
- `model/readiness/sequential` (under its accepted Rocq 9.3 compatibility patch), `analysis/definitions/sbf/{sbf,pred}` and `util/setoid` are compiled from the pinned tree.
- The proof-only facts imports are dropped.
- Recorded printer repairs make the readiness, job-preemption-model and FP-policy instances explicit where the elaborated statement leaves them implicit.
- **Implicit-instance check:** the extracted statement was printed with `Set Printing All` and compared with the official print. It is identical up to display qualifiers, except that the official print names the section-local `sequential_readiness` where the extraction shows its body `sequential_ready_instance … arr_seq`.

The fingerprints match (3/3).

## Validation

- **Spec** `results_rta_rs_fp_limited_preemptive.json`; base run `analysis_abstract_restricted_supply_bounded_bi_fp_final`.
- **Oleans:** the accepted oleans of the closure are hash-checked artifacts. 53 of 54 fixture oleans were reused from the verified content-addressed cache.
- **Export:** 146,668 lines. The export root is the accepted restricted-supply FP bounded-busy-interval root (without statements), merged with the accepted FP search-space root and the accepted limited-preemptive job, task and schedule model roots, plus the two definitions and the statement.
- **Chain:** the accepted restricted-supply FP bounded-busy-interval chain with the accepted FP search-space certificate and the accepted limited-preemptive model certificates.
  - `BoundedBiFpCorrespondence` and `SearchSpaceFpCorrespondence` are helper-only copies, shared with the accepted fully preemptive RTA run.

Attempts:
- **Prepare attempt 1** was archived as `…_attempt1_missing_export_targets`. The export lacked `nthD` and `limited_preemptions_rtc_threshold`, which the limited-preemptive model certificates reference. The pipeline's imported-symbol preflight caught this before any chain compile, and the model export roots were merged into the configuration.
- **Finalization attempt 1** (`rtafplp_final_attempt1_section_arg_order.log`) failed in the main certificate: a call to `lp_limited_preemptive_job_model_related` passed the job-cost inputs, which that section lemma does not take. The same call was corrected in the five sibling certificates.
- **Finalization attempt 2** (`rtafplp_final_attempt2_alias_allowlist.log`) stopped at the assumption audit on the helper aliases `LPC`/`SLPC`/`TLPC.I.{True,HEq,HEq_inst1}`, which were added to the UIP allowlist. No other assumption was reported.
- Each re-check reused the compiled chain prefix from its checkpoints: 67 modules on the first re-check, then all 69.

Certificate `RtaRsFpLimitedPreemptiveCorrespondence.v`. Leading inputs:
- `task_cost`, `job_cost` and `job_arrival` pointwise;
- `max_arrivals` by the accepted `CvMaxArrivalsRel`;
- task preemption points by the accepted `TppPointsRel`;
- job preemption points by the accepted `LpJobPreemptionPointsRel`;
- `job_task` by the accepted `AdJobTaskRel`;
- the processor state by the accepted two-sided `SvcProcessorStateRel` together with the pointwise `supply_on` relation.

Covered in both directions: FP policies, supply bound functions, task sets, arrival sequences, schedules, tasks, jobs and instants.

What is related, and how:
- **The sequential readiness model:** at each related schedule pair, from the accepted pending and `prior_jobs_complete` relations.
- **The limited-preemptive job model:** from the accepted limited-preemptive model certificate at the related preemption points.
- **The task model:** from the task preemption points through the accepted conversion to maximum non-preemptive segments.
- **`task_last_nonpr_segment`:** the accepted certificate.
- **The schedule's preemption model and the fixed-preemption-points validity:** the accepted certificates.
- **The FP blocking bound:** the accepted certificate.
- **Schedule validity and work conservation:** the accepted restricted-supply helper relations at that readiness model.
- **The FP policy at preemption points:** the priority-driven relation replayed at the schedule pair.
- **The accepted certificates, re-instantiated at this artifact:** the classical busy-SBF validity, the supply-bound-function predicates, the FP search space, the RBFs and the task response-time bound.

No source or target theorem is used.

Audit: 13 certificates (the two definitions, the statement and the helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **254 / 357 files**, **1712 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
