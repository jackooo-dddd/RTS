# results/rta/ovh/fp/limited_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-05 02:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ovh/fp/limited_preemptive.v`; rank 321.
- Public declarations: **3**:
  - definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - theorem `uniprocessor_response_time_bound_limited_fp`.
- Dependencies (all accepted): the restricted-supply FP analysis (bounded busy interval for FP, the FP search space, the intra-interference bound), the FP blocking bound, the limited-preemptive (fixed preemption points) task, job and schedule models, the sequential readiness facts, the task-cost facts, the valid task arrival sequence, the overheads schedule facts, and the overheads FP SBF (`analysis/facts/model/overheads/sbf/fp.v`).

## Translation

`Prosa/Results/Rta/Ovh/Fp/LimitedPreemptive.lean`. It gives a response-time analysis for fixed-priority scheduling with fixed preemption points of arrival-curve tasks on a uniprocessor subject to dispatch, context-switch and cache-related preemption overheads:
- **Busy-window recurrence:** requires `overhead_bound L + blocking_bound ts tsk + total_hep_request_bound_function_FP ts tsk L ≤ L`.
- **Response-time recurrence:** requires, for every offset `A` of the FP search space, a fixpoint `F` with
  - `overhead_bound F + blocking_bound ts tsk + (task_request_bound_function tsk (A + 1) - (task_last_nonpr_segment tsk - 1)) + total_ohep_request_bound_function_FP ts tsk F ≤ F`, and
  - `F + (overhead_bound (A + R) - overhead_bound F) + (task_last_nonpr_segment tsk - 1) ≤ A + R`.
- The overhead bound is `(DB + CSB + CRPDB) * (1 + 2 * Σ_{tsk_o ∈ ts, hep_task tsk_o tsk} max_arrivals tsk_o Δ)`; the blocking bound is taken at the maximum nonpreemptive segments derived from the task preemption points.

Binders follow the elaborated source types:
- the processor model is the explicit-overhead processor state;
- `basic_ready_instance` and `limited_preemptive_job_model` are passed explicitly; the FP policy acts on jobs through the accepted `FP_to_JLFP`;
- the source's section-local `overhead_bound` (a `Let`) is a `let` in both definitions, as in their elaborated bodies.

The proof instantiates the accepted restricted-supply limited-preemptive FP theorem with the overheads processor model and the accepted slowed FP overhead SBF. Its validity and unit-supply facts are the accepted overheads SBF facts; the limited-preemptive job model is a valid preemption model for schedules respecting it by the accepted fact. That theorem is stated for the sequential readiness model. Its validity, work conservation and policy compliance follow from those of the basic readiness model together with the sequential-tasks hypothesis; four private helpers prove this (a sequential-readiness backlog is a basic one, and every earlier job of the task is complete by `sequential_tasks`). The busy-window condition carries over because the slowed blackout bound never exceeds the blackout bound (`slowed_never_exceeds`), and the blackout bound is the overhead bound. For the response-time recurrence, as in the source, the solution `F` is shifted to a point `δ ≤ F` of equal slowed supply (`slowed_subtraction_value_preservation`). The other-higher-or-equal-priority RBF is monotone (the accepted fact), and so is the blackout bound; together with `bound_preserved_under_slowed` they give the run-to-completion tail. A private helper packages this step. Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaOvhFpLimitedPreemptiveSemanticSource`:
- The two definitions are byte-identical computational blocks, with the section context including the `overhead_bound` Let.
- The theorem is the authoritative elaborated type (proof omitted).
- **Hash-checked accepted `.vo` modules:**
  - the overheads FP SBF statements module (base run);
  - the accepted schedulability, request-bound-function, FP blocking-bound, FP search-space, limited-preemptive task, job and schedule, and task preemption-parameter modules.
- **Compiled from the pinned tree:** `model/task/absolute_deadline`, `analysis/abstract/search_space` (under its accepted Rocq 9.3 compatibility patch), `model/composite/valid_task_arrival_sequence` and `model/task/sequentiality`, with the accepted preemption-parameter shim.
- **Printer repairs:**
  - the implicit readiness instance and the section-local limited-preemptive job model (in the policy and preemption-model hypotheses), as in the accepted siblings, with their other arguments left to elaboration;
  - the recorded own-module-qualifier repairs `ovh.fp.limited_preemptive.*`. The official statement names this file's definitions module-qualified, because the restricted-supply FP definitions of the same names are also in scope there.

The fingerprints match: the definitions exactly modulo the own module qualifier, the theorem with its body equal modulo it. The theorem also equals the official `Set Printing All` print modulo module qualifiers.

## Validation

- **Spec** `results_rta_ovh_fp_limited_preemptive.json`; base run `analysis_facts_model_overheads_sbf_fp_final`.
- **Oleans:** hash-checked artifacts; 44 of 45 fixture oleans reused from the verified cache.
- **Export:** 154,364 lines; Rocq import in 51 s. The export root merges the accepted overheads FP SBF root and the accepted FP search-space root, plus the two definitions and the theorem.

Certificate chain:
- the overheads replay of the chain helpers for this export;
- the accepted arrival-curve, request-bound-function, FP blocking-bound and FP search-space certificates, re-bound to this export and to the replayed arrivals modules. The search-space copy keeps only its definition certificate: its statement correspondence, the statement-only section inputs and interference-bound `Let`, and its workload-bound import are dropped, as recorded in its header;
- the accepted job- and task-level limited-preemptive certificates of the restricted-supply limited-preemptive FP chain, re-bound likewise; the task-level copy drops its helper for the task run-to-completion threshold, which is not part of this export;
- the accepted schedule-change, overheads and overhead-resource-model modules;
- `RtaOvhFpLimitedPreemptiveCorrespondence.v`.

Attempts:
- **Prepare** passed on the first attempt. The accepted interface definition `NondecreasingInterface.nthD`, used by the re-bound job-level limited-preemptive certificate, is an export target, as in the EDF sibling.
- **Finalization** was accepted on the first attempt; the helper aliases of the re-bound modules were already on the UIP allowlist from the accepted siblings.

Certificate. Leading inputs, related by the accepted relations, each with two-way totals:
- the task and job types;
- the task-cost, arrival-curve, task-preemption-point, job-task, job-cost, job-arrival and job-preemption-point instances.

Covered in both directions:
- task sets;
- FP policies (pointwise on Booleans);
- arrival sequences;
- schedules (`ovh_psrel`).

The overhead bounds and the busy-window, response-time, offset and fixpoint values are related by `SubNatRel`.

How the ingredients are related:
- **The definitions:** unfolded on both sides. The filtered sum goes through the accepted filter relation. The RBFs (task, higher-or-equal and other-higher-or-equal priority), the FP `blocking_bound` (at the maximum nonpreemptive segments derived from the task preemption points, by the accepted conversion certificate; `task_last_nonpr_segment` likewise) and the FP `is_in_search_space` come from their accepted certificates.
- **`valid_task_arrival_sequence`:** unfolds into the accepted arrival-sequence, job-cost, task-set and arrival-curve relations.
- **`FP_to_JLFP`:** related as a JLFP policy through `job_task`.
- **Task-priority reflexivity and transitivity:** related pointwise.
- **`valid_fixed_preemption_points_model`:** by the accepted job- and task-level certificates.
- **The limited-preemptive job model:** by the accepted certificate.
- **`schedule_respects_preemption_model`:** unfolds over the accepted arrival, service, preemption-point and scheduled relations at the schedule pair.
- **`sequential_tasks`:** unfolds into the accepted arrival, `same_task`, scheduled and completion relations at the schedule pair.
- **Schedule hypotheses:** as in the accepted overheads SBF certificates; the overhead-resource model through the constructor-wise bridge.
- **`task_response_time_bound`:** through the accepted `completed_by` certificate.

No source or target theorem is used.

Audit: 22 certificates (the three declarations and nineteen helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **299 / 357 files**, **1877 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
