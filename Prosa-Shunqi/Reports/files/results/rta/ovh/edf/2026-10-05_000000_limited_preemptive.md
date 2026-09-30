# results/rta/ovh/edf/limited_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-05 00:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ovh/edf/limited_preemptive.v`; rank 316.
- Public declarations: **3**:
  - definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - theorem `uniprocessor_response_time_bound_limited_edf`.
- Dependencies (all accepted): the restricted-supply EDF analysis (bounded busy interval for EDF, the EDF search space, the intra-interference bound), the EDF priority, blocking-bound, busy-window and athep-workload facts, the limited-preemptive (fixed preemption points) task, job and schedule models, the task-cost and readiness facts, the valid task arrival sequence, the overheads schedule facts, and the overheads JLFP SBF (`analysis/facts/model/overheads/sbf/jlfp.v`).

## Translation

`Prosa/Results/Rta/Ovh/Edf/LimitedPreemptive.lean`. It gives a response-time analysis for EDF with fixed preemption points scheduling of arrival-curve tasks on a uniprocessor subject to dispatch, context-switch and cache-related preemption overheads:
- **Busy-window recurrence:** requires `overhead_bound L + total_request_bound_function ts L ≤ L` and `overhead_bound L + longest_busy_interval_with_pi ts tsk ≤ L`.
- **Response-time recurrence:** requires, for every offset `A` of the EDF search space, a fixpoint `F` with
  - `overhead_bound F + blocking_bound ts tsk A + (task_request_bound_function tsk (A + 1) - (task_last_nonpr_segment tsk - 1)) + bound_on_athep_workload ts tsk A F ≤ F`, and
  - `F + (overhead_bound (A + R) - overhead_bound F) + (task_last_nonpr_segment tsk - 1) ≤ A + R`.
- The overhead bound is `(DB + CSB + CRPDB) * (1 + 2 * Σ_{tsk_o ∈ ts} max_arrivals tsk_o Δ)`; the task-level bounds are taken at the maximum nonpreemptive segments derived from the task preemption points.

Binders follow the elaborated source types:
- the processor model is the explicit-overhead processor state;
- `basic_ready_instance`, `limited_preemptive_job_model` and the EDF instance with deadlines from the task deadlines are passed explicitly;
- the source's section-local `overhead_bound` (a `Let`) is a `let` in both definitions, as in their elaborated bodies.

The proof instantiates the accepted restricted-supply limited-preemptive EDF theorem with the overheads processor model and the accepted slowed JLFP overhead SBF. Its validity (for the EDF policy, with the limited-preemptive model valid by the accepted fact for schedules respecting it) and unit-supply facts are the accepted overheads SBF facts. The busy-window conditions carry over because the slowed blackout bound never exceeds the blackout bound (`slowed_never_exceeds`), and the blackout bound is the overhead bound. For the response-time recurrence, as in the source, the solution `F` is shifted to a point `δ ≤ F` of equal slowed supply (`slowed_subtraction_value_preservation`). The athep workload bound is monotone (the accepted fact), and so is the blackout bound; together with `bound_preserved_under_slowed` they give the run-to-completion tail. A private helper packages this step. Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaOvhEdfLimitedPreemptiveSemanticSource`:
- The two definitions are byte-identical computational blocks, with the section context including the `overhead_bound` Let.
- The theorem is the authoritative elaborated type (proof omitted).
- **Hash-checked accepted `.vo` modules:**
  - the overheads JLFP SBF statements module (base run);
  - the accepted schedulability, request-bound-function, EDF search-space, EDF blocking-bound, EDF athep-workload-bound, limited-preemptive task, job and schedule, EDF busy-window-bound and task preemption-parameter modules.
- **Compiled from the pinned tree:** `model/task/absolute_deadline`, `analysis/abstract/search_space` (under its accepted Rocq 9.3 compatibility patch), `model/composite/valid_task_arrival_sequence` and `model/priority/edf`, with the accepted preemption-parameter shim.
- **Printer repairs:**
  - the implicit readiness instance and the section-local limited-preemptive job model (in the policy and preemption-model hypotheses), as in the accepted siblings, with their other arguments left to elaboration;
  - the recorded own-module-qualifier repairs `ovh.edf.limited_preemptive.*`. The official statement names this file's definitions module-qualified, because the restricted-supply EDF definitions of the same names are also in scope there.

The fingerprints match: the definitions exactly modulo the own module qualifier, the theorem with its body equal modulo it. The theorem also equals the official `Set Printing All` print modulo module qualifiers.

## Validation

- **Spec** `results_rta_ovh_edf_limited_preemptive.json`; base run `analysis_facts_model_overheads_sbf_jlfp_final`.
- **Oleans:** hash-checked artifacts; all 45 fixture oleans reused from the verified cache.
- **Export:** 154,823 lines; Rocq import in 49 s. The export root merges the accepted overheads JLFP SBF root and the accepted EDF search-space root, plus the two definitions and the theorem.

Certificate chain:
- the overheads replay of the chain helpers for this export;
- the accepted arrival-curve, request-bound-function, EDF athep-workload-bound, EDF blocking-bound and EDF search-space certificates, re-bound to this export and to the replayed arrivals modules. The search-space copy keeps only its definition certificate: its statement correspondence, the statement-only interference-bound `Let` and its workload-bound import are dropped, as recorded in its header;
- the accepted job- and task-level limited-preemptive certificates and the EDF busy-window-bound certificate of the restricted-supply limited-preemptive EDF chain, re-bound likewise. The task-level copy drops its helper for the task run-to-completion threshold, which is not part of this export. For the busy-window bound: Its `bigMaxListCond` constructor equations are taken from the accepted EDF blocking-bound export root of this export. Their kernel-checked Lean statements are identical to those of the root it originally used; this is recorded in its header;
- the accepted schedule-change, overheads and overhead-resource-model modules;
- `RtaOvhEdfLimitedPreemptiveCorrespondence.v`.

Attempts:
- **Prepare attempt 1** passed but was archived as `…_attempt1_missing_interface_target`, with its log. The re-bound job-level limited-preemptive certificate uses the accepted interface definition `NondecreasingInterface.nthD`, which was not an export target; it was added to the export targets.
- **Prepare attempt 2** passed.
- **Finalization attempt 1** stopped at the assumption audit (log archived as `rovhedflp_finalize_attempt1_helper_aliases.log`). The only findings were helper aliases `X.I.{True,HEq,HEq_inst1}` of the re-bound limited-preemptive modules, which were added to the UIP allowlist.
- **Finalization attempt 2** was accepted.

Certificate. Leading inputs, related by the accepted relations, each with two-way totals:
- the task and job types;
- the task-cost, task-deadline, arrival-curve, task-preemption-point, job-task, job-cost, job-arrival and job-preemption-point instances.

Covered in both directions:
- task sets;
- arrival sequences;
- schedules (`ovh_psrel`).

The overhead bounds and the busy-window, response-time, offset and fixpoint values are related by `SubNatRel`.

How the ingredients are related:
- **The definitions:** unfolded on both sides. The RBFs, `bound_on_athep_workload`, `blocking_bound`, `longest_busy_interval_with_pi` and the EDF `is_in_search_space` come from their accepted certificates, at the maximum nonpreemptive segments derived from the task preemption points (by the accepted conversion certificate); `task_last_nonpr_segment` likewise.
- **`valid_task_arrival_sequence`:** unfolds into the accepted arrival-sequence, job-cost, task-set and arrival-curve relations.
- **The EDF policy:** related pointwise from the arrival and deadline inputs.
- **`valid_fixed_preemption_points_model`:** by the accepted job- and task-level certificates.
- **The limited-preemptive job model:** by the accepted certificate.
- **`schedule_respects_preemption_model`:** unfolds over the accepted arrival, service, preemption-point and scheduled relations at the schedule pair.
- **Schedule hypotheses:** as in the accepted overheads SBF certificates; the overhead-resource model through the constructor-wise bridge.
- **`task_response_time_bound`:** through the accepted `completed_by` certificate.

No source or target theorem is used.

Audit: 17 certificates (the three declarations and fourteen helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **297 / 357 files**, **1871 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
