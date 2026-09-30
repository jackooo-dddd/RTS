# results/rta/exc/fp/fully_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-10-05 05:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/exc/fp/fully_nonpreemptive.v`; rank 307.
- Public declarations: **3**:
  - definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - theorem `uniprocessor_response_time_bound_fully_nonpreemptive_fp`.
- Dependencies (all accepted): the restricted-supply FP analysis (bounded busy interval for FP, the FP search space, the intra-interference bound), the sequential readiness facts, the fully nonpreemptive task and run-to-completion facts, the valid task arrival sequence, and the exceedance SBF (`analysis/facts/model/exceedance/SBF.v`).

## Translation

`Prosa/Results/Rta/Exc/Fp/FullyNonpreemptive.lean`. It gives a response-time analysis for fully nonpreemptive fixed-priority scheduling of arrival-curve tasks on an ideal uniprocessor with exceedance executions. The exceedance within every busy-interval prefix of the task under analysis is bounded by `e`.
- **Busy-window recurrence:** requires `e < L` and `blocking_bound ts tsk + total_hep_request_bound_function_FP ts tsk L + e ≤ L`.
- **Response-time recurrence:** requires, for every offset `A` of the FP search space, a fixpoint `F` with
  - `blocking_bound ts tsk + (task_request_bound_function tsk (A + 1) - (task_cost tsk - 1)) + total_ohep_request_bound_function_FP ts tsk F + e ≤ F`, and
  - `F + (task_cost tsk - 1) ≤ A + R`.

Binders follow the elaborated source types:
- the processor model is the accepted exceedance processor state;
- the source's section-local instances are the accepted `sequential_ready_instance arr_seq` (the local `sequential_readiness`), `fully_nonpreemptive_job_model` and `fully_nonpreemptive_task_model`, passed explicitly;
- the FP policy acts on jobs through the accepted `FP_to_JLFP`;
- the interval sum of the exceedance hypothesis is the `Finset.Ico` sum over `Nat` (= `instant`).

The proof instantiates the accepted restricted-supply fully nonpreemptive FP theorem:
- with the exceedance processor model, whose uniprocessor, unit-supply and full-consumption properties are the accepted facts;
- with the accepted SBF `EPS_SBF_inst e = Δ - e`, valid and unit by the accepted facts of `analysis/facts/model/exceedance/SBF.v`.

The recurrences carry over because the SBF is the interval length minus `e`. Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaExcFpFullyNonpreemptiveSemanticSource`:
- The two definitions are byte-identical computational blocks.
- The theorem is the authoritative elaborated type (proof omitted).
- The source-local sequential readiness instance is extracted byte-identically as a helper block. It is made explicit, together with the section-local fully nonpreemptive job model, by recorded printer repairs whose other arguments are left to elaboration.
- The recorded own-module-qualifier repairs `exc.fp.fully_nonpreemptive.*` apply to the two definitions.
- **Hash-checked accepted `.vo` modules:**
  - the exceedance SBF module (base run);
  - the schedulability, request-bound-function, FP blocking-bound, FP search-space, fully nonpreemptive task-model and task preemption-parameter modules.
- **Compiled from the pinned tree:**
  - `model/task/absolute_deadline`;
  - `analysis/abstract/search_space` and `model/readiness/sequential` (under their accepted Rocq 9.3 compatibility patches);
  - `model/composite/valid_task_arrival_sequence`, `model/preemption/fully_nonpreemptive`, `model/schedule/nonpreemptive` and `model/task/sequentiality`;
  - the accepted preemption-parameter shim.

The fingerprints match: the definitions exactly modulo the own module qualifier, the theorem with its body equal modulo it. The theorem also equals the official `Set Printing All` print modulo module qualifiers.

## Validation

- **Spec** `results_rta_exc_fp_fully_nonpreemptive.json`; base run `analysis_facts_model_exceedance_sbf_final`.
- **Export root:** the accepted exceedance SBF root (with its exceedance-processor witnesses and closed forms) merged with the accepted FP search-space root, plus the two definitions and the theorem. The theorem type's interval sum is projected by the exporter to `List.foldr Nat.add` over `List.range'` (checked definitionally equal), as for the exceedance SBF statements.
- **Oleans:** hash-checked artifacts; 34 of 35 fixture oleans reused from the verified cache.
- **Export:** 149,921 lines; Rocq import in 47 s.

Certificate chain:
- the accepted generic chain helpers replayed at the exceedance processor's universe instance of this export (`Exc*.v`);
- the accepted concrete state relation `ExcStateRel.v`;
- the accepted arrival-curve, request-bound-function, FP blocking-bound and FP search-space certificates, re-bound to this export and to the replayed arrivals modules. The search-space copy keeps only its definition certificate: its statement correspondence, the statement-only section inputs and interference-bound `Let`, and its workload-bound import are dropped, as recorded in its header;
- `RtaExcFpFullyNonpreemptiveCorrespondence.v`.

Attempts:
- **Prepare** passed on the first attempt.
- **Finalization attempt 1** stopped at the assumption audit (log archived as `rexcfpnp_finalize_attempt1_helper_aliases.log`). The only findings were helper aliases `X.I.{True,HEq_inst1}` of the re-bound modules, which were added to the UIP allowlist.
- **Finalization attempt 2** was accepted.

Certificate. Leading inputs, related by the accepted relations, each with two-way totals:
- the task and job types;
- the task-cost, arrival-curve, job-task, job-cost and job-arrival instances.

Covered in both directions:
- task sets;
- FP policies (pointwise on Booleans);
- arrival sequences;
- schedules (`exc_psrel`).

Tasks and jobs are related by identity; the budget and the busy-window, response-time, offset and fixpoint values by `SubNatRel`.

How the ingredients are related:
- **The definitions:** unfolded on both sides. The RBFs, the FP `blocking_bound` (at the fully nonpreemptive task model, related pointwise through `task_cost`) and the FP `is_in_search_space` come from their accepted certificates.
- **`valid_task_arrival_sequence`:** unfolds into the accepted arrival-sequence, job-cost, task-set and arrival-curve relations.
- **The sequential readiness instance:** related pointwise at the schedule pair, through the accepted `pending` relation and `prior_jobs_complete` (the accepted `task_arrivals_before` and `completed_by` relations).
- **`FP_to_JLFP`:** related as a JLFP policy through `job_task`.
- **Task-priority reflexivity and transitivity:** related pointwise.
- **The fully nonpreemptive job model:** related pointwise through `job_cost`.
- **`nonpreemptive_schedule`:** unfolds over the accepted scheduled and completion relations.
- **The exceedance hypothesis:** through the replayed classical busy-interval-prefix relation, the accepted interval-sum and `nat_of_bool` relations, and `is_exceedance_exec` constructor-wise.
- **`task_response_time_bound`:** through the accepted `completed_by` certificate.

No source or target theorem is used.

Audit: 21 certificates (the three declarations and eighteen helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **302 / 357 files**, **1887 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
