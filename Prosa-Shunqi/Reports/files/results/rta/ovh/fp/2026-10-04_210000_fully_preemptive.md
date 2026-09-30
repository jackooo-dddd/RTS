# results/rta/ovh/fp/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-04 21:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ovh/fp/fully_preemptive.v`; rank 320.
- Public declarations: **3**:
  - definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - theorem `uniprocessor_response_time_bound_fully_preemptive_fp`.
- Dependencies (all accepted): the restricted-supply FP analysis (bounded busy interval for FP, the FP search space, the intra-interference bound), the fully preemptive task and job models, the sequential readiness facts, the task-cost facts, the valid task arrival sequence, the overheads schedule facts, and the overheads FP SBF (`analysis/facts/model/overheads/sbf/fp.v`).

## Translation

`Prosa/Results/Rta/Ovh/Fp/FullyPreemptive.lean`. It gives a response-time analysis for fully preemptive fixed-priority scheduling of arrival-curve tasks on a uniprocessor subject to dispatch, context-switch and cache-related preemption overheads:
- **Busy-window recurrence:** requires `overhead_bound L + total_hep_request_bound_function_FP ts tsk L ≤ L`.
- **Response-time recurrence:** requires a fixpoint `F` with `overhead_bound F + task_request_bound_function tsk (A + 1) + total_ohep_request_bound_function_FP ts tsk F ≤ F ≤ A + R` for every offset `A` of the FP search space.
- The overhead bound is `(DB + CSB + CRPDB) * (1 + 2 * Σ_{tsk_o ∈ ts, hep_task tsk_o tsk} max_arrivals tsk_o Δ)`.

Binders follow the elaborated source types:
- the processor model is the explicit-overhead processor state;
- `basic_ready_instance` and `fully_preemptive_job_model` are passed explicitly; the FP policy acts on jobs through the accepted `FP_to_JLFP`;
- the source's section-local `overhead_bound` (a `Let`) is a `let` in both definitions, as in their elaborated bodies.

The proof instantiates the accepted restricted-supply fully preemptive FP theorem with the overheads processor model and the accepted slowed FP overhead SBF. Its validity, monotonicity and unit-supply facts are the accepted overheads SBF facts; the fully preemptive model is a valid preemption model by the accepted fact. That theorem is stated for the sequential readiness model. Its validity, work conservation and policy compliance follow from those of the basic readiness model together with the sequential-tasks hypothesis; four private helpers prove this (a sequential-readiness backlog is a basic one, and every earlier job of the task is complete by `sequential_tasks`). The recurrences carry over because the slowed blackout bound never exceeds the blackout bound (`slowed_never_exceeds`), and the blackout bound is the overhead bound. Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaOvhFpFullyPreemptiveSemanticSource`:
- The two definitions are byte-identical computational blocks, with the section context including the `overhead_bound` Let.
- The theorem is the authoritative elaborated type (proof omitted).
- **Hash-checked accepted `.vo` modules:**
  - the overheads FP SBF statements module (base run);
  - the accepted schedulability, request-bound-function, FP blocking-bound, FP search-space, fully preemptive task-model and task preemption-parameter modules.
- **Compiled from the pinned tree:** `model/task/absolute_deadline`, `analysis/abstract/search_space` (under its accepted Rocq 9.3 compatibility patch), `model/composite/valid_task_arrival_sequence`, `model/preemption/fully_preemptive` and `model/task/sequentiality`, with the accepted preemption-parameter shim.
- **Printer repairs:**
  - the implicit readiness instance and the section-local fully preemptive job model, as in the accepted siblings, with their other arguments left to elaboration;
  - the recorded own-module-qualifier repairs `ovh.fp.fully_preemptive.*`. The official statement names this file's definitions module-qualified, because the restricted-supply FP definitions of the same names are also in scope there.

The fingerprints match: the definitions exactly modulo the own module qualifier, the theorem with its body equal modulo it. The theorem also equals the official `Set Printing All` print modulo module qualifiers.

## Validation

- **Spec** `results_rta_ovh_fp_fully_preemptive.json`; base run `analysis_facts_model_overheads_sbf_fp_final`.
- **Oleans:** hash-checked artifacts; 44 of 45 fixture oleans reused from the verified cache.
- **Export:** 153,669 lines; Rocq import in 92 s. The export root merges the accepted overheads FP SBF root and the accepted FP search-space root, plus the two definitions and the theorem.

Certificate chain:
- the overheads replay of the chain helpers for this export;
- the accepted arrival-curve, request-bound-function, FP blocking-bound and FP search-space certificates, re-bound to this export and to the replayed arrivals modules. The search-space copy keeps only its definition certificate: its statement correspondence, the statement-only section inputs and interference-bound `Let`, and its workload-bound import are dropped, as recorded in its header;
- the accepted schedule-change, overheads and overhead-resource-model modules;
- `RtaOvhFpFullyPreemptiveCorrespondence.v`.

Attempts:
- **Prepare** passed on the first attempt.
- **Finalization attempt 1** stopped at the assumption audit (log archived as `rovhfpfp_finalize_attempt1_helper_aliases.log`). The only findings were helper aliases `X.I.{True,HEq_inst1}` of the re-bound search-space module, which were added to the UIP allowlist.
- **Finalization attempt 2** was accepted.

Certificate. Leading inputs, related by the accepted relations, each with two-way totals:
- the task and job types;
- the task-cost, arrival-curve, job-task, job-cost and job-arrival instances.

Covered in both directions:
- task sets;
- FP policies (pointwise on Booleans);
- arrival sequences;
- schedules (`ovh_psrel`).

The overhead bounds and the busy-window, response-time, offset and fixpoint values are related by `SubNatRel`.

How the ingredients are related:
- **The definitions:** unfolded on both sides. The filtered sum goes through the accepted filter relation. The RBFs (task, higher-or-equal and other-higher-or-equal priority) and the FP `is_in_search_space` come from their accepted certificates.
- **`valid_task_arrival_sequence`:** unfolds into the accepted arrival-sequence, job-cost, task-set and arrival-curve relations.
- **`FP_to_JLFP`:** related as a JLFP policy through `job_task`.
- **Task-priority reflexivity and transitivity:** related pointwise.
- **The fully preemptive job model:** related pointwise.
- **`sequential_tasks`:** unfolds into the accepted arrival, `same_task`, scheduled and completion relations at the schedule pair.
- **Schedule hypotheses:** as in the accepted overheads SBF certificates; the overhead-resource model through the constructor-wise bridge.
- **`task_response_time_bound`:** through the accepted `completed_by` certificate.

No source or target theorem is used.

Audit: 21 certificates (the three declarations and eighteen helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **294 / 357 files**, **1862 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
