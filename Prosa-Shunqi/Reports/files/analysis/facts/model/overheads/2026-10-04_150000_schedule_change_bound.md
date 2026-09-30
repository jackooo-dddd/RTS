# analysis/facts/model/overheads/schedule_change_bound.v — canonical translation report

First experiment timestamp: **2026-10-04 15:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/model/overheads/schedule_change_bound.v`; rank 261.
- Public declarations: **3** lemmas: `schedule_changes_bounded_by_total_arrivals_JLFP`, `schedule_changes_bounded_by_total_arrivals_FP` and `schedule_changes_bounded_by_total_arrivals_FIFO`. The source's local helper lemmas are not public.
- Dependencies (all accepted):
  - `analysis/facts/completes_at.v` and `analysis/facts/model/arrival_curves.v`;
  - `analysis/facts/model/overheads/priority_bump.v` and `analysis/facts/model/overheads/schedule_change.v`;
  - `model/task/arrival/curves.v`.

## Translation

`Prosa/Analysis/Facts/Model/Overheads/ScheduleChangeBound.lean`. It bounds the number of schedule changes in `[t1 + 1, t1 + Δ)` of a busy-interval prefix of an explicit-overhead uniprocessor schedule (basic readiness, no superfluous preemptions):
- **JLFP:** twice the arrivals of all tasks in `Δ`.
- **FP:** twice the arrivals of the tasks with higher-or-equal priority.
- **FIFO:** once the arrivals of all tasks.

Binders follow the elaborated source types:
- `basic_ready_instance` is the accepted Lean definition passed explicitly.
- The policy coercions are the accepted `JLFP_to_JLDP` and `FP_to_JLFP`.
- MathComp sums over task sets are `sumSeq` and `sumFiltered`.
- `t1.+1` is `t1 + 1`.

The proof establishes the same facts as the source through a direct counting argument over the instants of `[t1 + 1, t)`:
1. Every schedule change is a priority bump or a job completion, using the no-superfluous-preemption property.
2. A completion of a lower-priority job is itself a priority bump: completion times are preemption times, and a higher-or-equal-priority job is scheduled right after.
3. Every higher-or-equal-priority job arriving in `[t1, t)` accounts for at most one bump and at most one completion:
   - it is the job scheduled at the bump, and two such bumps contradict `priority_higher_than_pending_job_priority`;
   - it completes at most once.
4. Under FIFO no bump occurs, via the accepted `no_priority_bumps_in_fifo`.
5. The final step uses the accepted `jlfp_/fp_hep_arrivals_bounded_by_sum_max_arrivals`.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `ScheduleChangeBoundSemanticSource`:
- The three statements are the authoritative elaborated types (proofs omitted).
- The accepted overheads priority-bump statements module is used (hash-checked `.vo`).
- `analysis/definitions/overheads/schedule_change` is compiled from the pinned tree.
- `model/task/arrival/curves` is the accepted compiled source of the base closure.
- The proof-only facts imports are dropped.
- **Printer repairs** (recorded): four make the implicit readiness instance explicit, for `valid_schedule`, `work_conserving` and `respects_JLFP/FP_policy_at_preemption_point`. Their other arguments are left to elaboration, because binder names differ between the statements.

Fingerprints: FIFO matches exactly; JLFP and FP match through a new, narrowly scoped display rule.
- **The display difference.** The official toolchain (MathComp 2.4) prints a big operator that is the right operand of `*` at the end of a type with parentheses, `2 * (\sum_(tsk <- ts) …)`. The validation toolchain (MathComp 2.6) prints the same term without them. This was reproduced in a plain MathComp environment on both switches: `2 * (\sum_(i <- r) F i)` against `2 * \sum_(i <- r) F i`.
- **The pipeline rule** `TYPE_EQUAL_MODULO_MATHCOMP_BIGOP_OPERAND_PARENS` joins the existing MathComp display rules. It accepts exactly the removal of one such final parenthesised `\sum_` operand, and requires the result to equal the extracted statement exactly. A group that is followed by anything is not touched. Pre-change backup: `translation_file_pipeline.pre_bigop.py`.
- **Independent check:** all three extracted statements equal the official `Set Printing All` prints modulo module qualifiers.

## Validation

- **Spec** `analysis_facts_model_overheads_schedule_change_bound.json`; base run `analysis_facts_model_overheads_priority_bump_final`.
- **Oleans:** hash-checked artifacts; 28 of 30 fixture oleans reused from the verified cache.
- **Export:** 151,624 lines; Rocq import in 110 s. The export root merges three accepted roots, plus the three statements:
  - the overheads priority-bump facts root (with both universe witness modules);
  - the schedule-change definitions root;
  - the arrival-curve facts root, with Lean's `funext` exported with its proof (as in the accepted FIFO facts file).

The overheads replay tool replays the chain helpers for this export, dropping only the 28 processor-model-cover constructions of `OvhPStateCoverHelpers`. The accepted arrival-curve certificate is re-bound onto the replayed arrivals modules (`OvhCurvesCorrespondence.v`; the curves do not depend on the processor model).

Attempts:
- **Prepare** passed on the first attempt. The chain compiled on the first check; the only fix was the module path of the extracted preemption-parameter definitions in the new main certificate.
- **Finalization attempt 1** stopped at the assumption audit (log archived as `scb_finalize_attempt1_helper_aliases.log`). The only findings were the helper aliases `OvhArrivalsCorrespondence.I.{True,HEq_inst1}` and `OvhCurvesCorrespondence.I.{True,HEq_inst1}`, which were added to the UIP allowlist.
- **Finalization attempt 2** was accepted.

Certificate `OverheadsScheduleChangeBoundCorrespondence.v`. Leading input: the job type; for FP, also the task type, the arrival curves and the FP policy (accepted relations with two-way totals). Covered in both directions:
- job-arrival, job-cost and preemption instances, JLFP policies, arrival sequences and schedules (`ovh_psrel`), as in the accepted priority-bump certificate;
- job-task maps and task sets;
- task types with their DecidableEq, MaxArrivals and JobTask instances quantified inside the JLFP and FIFO statements, through the exported `funext` (as in the accepted FIFO facts certificate).

How the ingredients are related:
- **Basic readiness:** related pointwise through `pending`.
- **`no_superfluous_preemptions`:** through `preempted_at`.
- **`number_schedule_changes`:** the accepted schedule-change certificate, via the constructor-wise bridge from `ovh_psrel`.
- **Arrival-curve and task-set predicates:** the accepted curve certificates.
- **Sums:** the accepted list-sum relations.

No source or target theorem is used.

Audit: 24 certificates (the three statements and twenty-one helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **288 / 357 files**, **1835 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
