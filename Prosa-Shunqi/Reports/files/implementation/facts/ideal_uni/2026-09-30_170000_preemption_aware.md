# implementation/facts/ideal_uni/preemption_aware.v — canonical translation report

First experiment timestamp: **2026-09-30 17:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/facts/ideal_uni/preemption_aware.v`; rank 202.
- Public declarations: **10**: `allocation_at_idle`, `idle_schedule_no_backlogged_jobs`, `np_schedule_work_conserving`, `np_schedule_jobs_from_arrival_sequence`, `chosen_job_is_ready`, `jobs_must_be_ready`, `np_schedule_valid`, `np_job_remains_scheduled`, `np_consistent`, `np_respects_preemption_model`.
- Dependencies (ideal-schedule facts, ideal uniprocessor scheduler, generic-schedule facts, ideal processor, limited-preemptive schedule, `util/tactics`): accepted.

## Translation

`Prosa/Implementation/Facts/IdealUni/PreemptionAware.lean`. Binders follow the elaborated types: each theorem takes only the section inputs and hypotheses it uses, in their elaborated order.

Conventions:
- Instance inputs quantified after a hypothesis are `∀ [..]` binders.
- `idle_state` is `none`.
- The section-local `sched_prefix`/`prefix` is inlined as a `match` on the instant.
- `j \in s` is `decide (j ∈ s) = true`, and `x == Some j` is `decide (x = some j) = true`.
- `t.+1`/`t.-1` are `t + 1`/`t - 1`.

Proofs follow the source:
- case analysis on the previous-job-nonpreemptive test;
- `schedule_up_to` unfolding, widening, prefix inclusion and emptiness beyond the horizon;
- backlog prefix invariance and nonclairvoyance of readiness;
- `np_respects_preemption_model` by induction on the instant.

Lean axioms: none beyond the standard ones.

## Source binding

The statements come from the authoritative elaborated types (module `PreemptionAwareSemanticSource`).
- The scheduler definitions are bound to the accepted `IdealUniSchedulerSemanticSource` of the base run.
- `schedule_respects_preemption_model` and `preemption_time` are bound to their accepted extracted sources. The `.vo` files are copied and hash-checked, and `model/schedule/scheduled` is compiled from the pinned tree.
- The proof-only imports are dropped.

Recorded printer repair: the printed prefix match loses the implicit processor model of `empty_schedule` (as an argument of `jobs_backlogged_at`), so the repair names it `(PState := ideal.processor_state Job)`. The statements print back to the unrepaired evidence.

All 10 statements match the evidence (fingerprint: 10 checked, 0 mismatches).

## Validation

Spec `implementation_facts_ideal_uni_preemption_aware.json`; base run `implementation_definitions_ideal_uni_scheduler_final`.

Artifacts: 14 accepted `.olean` files are copied and hash-checked against their manifests:
- `SchedulePrefix`, `Supply`, `Scheduled`, `Service` definitions/facts, `Model/Scheduled` facts, `Sequentiality`;
- `ReplaceAt`, `GenericSchedule`, `Ideal/Schedule`, `Readiness`, `Backlogged`;
- `LimitedPreemptive`, `PreemptionTime`.

Export: 149,714 lines. The export root:
- is the accepted ideal-uniprocessor-scheduler root, with its kernel-checked equations;
- adds the readiness, schedule-prefix, validity, work-conserving, preemption-time and limited-preemptive definitions, and the ten statements;
- adds no new equation.

Attempts:
- `attempt1_match_implicit_pstate`: the extracted statement did not elaborate, because of the lost implicit above. The printer repair was added.
- `attempt2_probe_word_split`: my generated fingerprint probe was malformed, because the shell did not split the name list. The fixtures were regenerated.

Both runs were archived.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter/IdealUniScheduler certificates, re-bound.
- The new `PreemptionAwareCorrespondence.v`. Inputs:
  - The ideal processor is fixed on both sides, with states related by the Option map and schedules pointwise.
  - `job_cost` by `SvcJobCostRel`, `job_arrival` by `ArJobArrivalRel`, and arrival sequences by `ArArrivalSequenceRel`.
  - The readiness model is related by `job_ready` on related schedules and instants.
  - The preemption model is related pointwise, and `choose_job` on related instants and job lists.
- Inner quantifiers are covered in both directions:
  - Schedules, job lists, preemption models and `choose_job` by explicit conversions.
  - Readiness models, which are quantified after a hypothesis in `np_schedule_work_conserving`/`np_consistent`, are covered among nonclairvoyant models. A nonclairvoyant `job_ready` respects pointwise-equal schedules, so a conditional cover suffices and no functional extensionality is needed. Each covering model is built from the other side's `job_ready`, with its pending obligation transported through the related `pending`.
- `preemption_time`/`scheduled_job_at` are related through the accepted filter and `arrivals_up_to` certificates, and `head?` on canonical lists.
- The inlined prefix match is closed by the accepted `empty_schedule`/`schedule_up_to` relations on the canonical constructors.
- No source or target theorem is used.

Audit: 41 certificates (10 principal, 31 helpers). All are certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. The observed `IdealUniSchedulerCorrespondence.I.{True,HEq,HEq_inst1}` aliases were allowlisted as SProp definitional UIP, like the other chain aliases.

## Formal acceptance

Coverage **192 / 357 files**, **1355 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
