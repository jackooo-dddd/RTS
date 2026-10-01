# implementation/refinements/EDF/nonpreemptive_sched.v — canonical translation report

First experiment timestamp: **2026-10-07 21:00:00 +08:00**

The twelfth file behind the CoqEAL build boundary. The inventory places it there, so its type evidence is the
official-toolchain CoqEAL evidence, as for `refinements.v`. The file itself does not use CoqEAL: its closure
contains no CoqEAL module.

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/refinements/EDF/nonpreemptive_sched.v`; layer 20; rank 348.
- **9 public declarations:**
  - the section's aliases `Task` and `Job`;
  - the `Instance basic_ready_instance`;
  - the definition `sched`;
  - the lemmas `sched_jobs_must_be_ready_to_execute`, `sched_nonpreemptive_next`, `sched_nonpreemptive` and
    `respects_policy_at_preemption_point_edf_np`, and the `Remark sched_valid`.
- **Dependencies (accepted):** `analysis/definitions/tardiness.v`, `analysis/facts/preemption/rtc_threshold/nonpreemptive.v`,
  `analysis/facts/preemption/task/nonpreemptive.v`, `analysis/facts/readiness/basic.v`,
  `implementation/definitions/task.v`, `implementation/facts/ideal_uni/prio_aware.v` and `model/priority/edf.v`.

## Translation

`Prosa/Implementation/Refinements/EDF/NonpreemptiveSched.lean` compiles with only the standard Lean axioms.

- **Aliases.** `Task` and `Job` (the concrete types as `eqType`s) are abbreviations of the accepted concrete types.
- **Instances.**
  - The source's `Instance basic_ready_instance` is a global instance, as in the source.
  - The section-local instances are passed explicitly to `uni_schedule`: this readiness model,
    `fully_nonpreemptive_job_model`, and `EDF` coerced to a JLDP policy.
  - `EDF Job` uses the job-deadline instance the source resolves, the accepted `job_deadline_from_task_deadline`
    (arrival plus task deadline). The concrete job's own `job_deadline` field is not an instance in the source
    either.
- **Binders.** The section's `arr_seq` and `H_valid_arrivals` are explicit binders, in the order of the elaborated
  types. `sched_valid` does not take `H_valid_arrivals`: its elaborated type does not.
- **Proofs** follow the source:
  - readiness via the accepted `jobs_must_be_ready` with `supremum_in`;
  - validity via the accepted `np_schedule_jobs_from_arrival_sequence`;
  - `sched_nonpreemptive_next` unfolds `allocation_at` at `t + 1` and relates the prefix service to the schedule's
    service with the accepted `schedule_up_to_prefix_inclusion` / `schedule_up_to_identical_prefix`; a private
    lemma `service_of_identical_prefix` (LEAN_HELPER) replaces the source's `eq_big_nat` rewriting;
  - `sched_nonpreemptive` by induction on `t'` with the accepted `completion_monotonic`, as in the source;
  - the policy statement via the accepted `schedule_respects_policy`.

## Source binding

Source mode `official_closure`, with the run's CoqEAL build.
- **Closure:** `Validation/tooling/proof_closure/refinements_EDF_nonpreemptive_sched_closure.txt`.
- **Patch:** `…-refinements-EDF_nonpreemptive_sched.patch`, proof-only. It also adds the file-local
  `Set SsrOldRewriteGoalsOrder.` to the module.
- **Module change:** the spec opts in with `official_closure.module_change: "rewrite_goals_order_flag"`. It is
  checked line by line and recorded in the manifest.

### Type fingerprints

9/9 are `EXACT_MODULO_OWN_MODULE_QUALIFIER`. The official evidence context loads the four `*_sched.v` files,
which declare the same short names, so it prints this file's own names qualified by their module
(`EDF.nonpreemptive_sched.Job`, `nonpreemptive_sched.basic_ready_instance`, …), both at the head and inside the types. Exactly those names are listed in the spec's
`own_qualified_in_type`.

## Validation

- **Spec:** `implementation_refinements_EDF_nonpreemptive_sched.json`.
- **Lean base run:** `implementation_refinements_EDF_preemptive_sched_final`, with the accepted oleans of the scheduler
  closure (each checked against its accepted manifest).
- **Export:** 155,422 lines. Its root is the file's 4 definitions with bodies and its 5 statements statement-only,
  plus:
  - the accepted ideal-uniprocessor-scheduler export root (the export configuration of `prio_aware.v` without its
    statements): the Service / Schedule interfaces, the ideal processor, the generic scheduler, the
    work-conserving backlog, and the kernel-checked `schedule_up_to` / `empty_schedule` / `replace_at` and
    ideal-state equations;
  - the accepted concrete task and job definitions and their arrival-curve closure, with the accepted
    extrapolated-arrival-curve arithmetic laws;
  - **new shared fixture `RefSchedComputationInterface.lean`.** Twelve equations: the accepted `BigcatInterface`
    (`bigCat`, `filter`) and `IdealUniSchedulerInterface` equations, instantiated at the concrete job type. Each is
    proved by the accepted generic equation and exported with its proof. They are needed because the statements
    use the concrete (universe-0) copies of these definitions, which the generic equations do not mention. No new
    equation is added.

### Certificate chain (9 modules)

- **7 re-bound accepted modules.** Every kept command is unchanged; only the imported module is renamed.
  - From `implementation/facts/job_constructor.v`: `PsEac`, `PsAb`, `PsImplTask` and `PsListOps`. These provide the
    concrete task and job relations `ItTaskRel` / `ItJobRel` (the graph of the accepted export map, with two-way
    totals) and the list relations at the concrete list copies.
  - From `implementation/facts/ideal_uni/prio_aware.v`: `PsSvcBase`, `PsSvcNatBool` and `PsSvcInterval` (Booleans,
    the Nat operations, and the half-open service sum).
- **`PsSched.v` (shared by the four `*_sched.v` files; byte-identical to the copy in the accepted
  `EDF/preemptive_sched.v` certificate except for the imported module name).**
  - **Why it is needed.** The accepted scheduler certificates relate the same job type on both sides. These files
    fix the job type to the concrete jobs, which are a different Rocq type on each side.
  - **Relations.** Jobs by `ItJobRel`; optional jobs by the constructor-preserving map; job lists by mapping the
    export and then the accepted `ArListRel`, so the accepted membership and uniqueness certificates apply at the
    compiled job type (an equality type transported along the accepted import map); arrival sequences and
    schedules pointwise.
  - **Proofs** follow the accepted ideal-uniprocessor-scheduler, preemption-aware and priority-aware certificates,
    with the identity job carrier replaced by `ItJobRel`. They cover the ideal states, `scheduled_at`, the service
    sum, `completed_by`, `pending`, arrivals (`bigCat`), `filter`, membership and `valid_arrival_sequence`,
    `prev_job_nonpreemptive`, the backlog, `allocation_at`, the generic schedule (by induction through the
    kernel-checked equations), `supremum` / `choose_highest_prio_job`, `uni_schedule`, `preemption_time`, and the
    schedule-level `valid_schedule` / `respects_JLDP_policy_at_preemption_point`.
  - The readiness model, preemption model and policy are parameters, related by hypotheses.
- **`RefEDFNPSchedCorrespondence.v` (new).**
  - Principal totals for `Task` and `Job`.
  - Basic readiness, related through `pending`.
  - The fully-nonpreemptive model: its two equality tests on the service (`ρ == 0 || ρ == job_cost j`).
  - EDF: the deadline comparison, through the job-deadline instance derived from the task deadline.
  - `sched`, for related arrival sequences.
  - The five statements. `sched_nonpreemptive_next` and `sched_nonpreemptive` share one step lemma: scheduled at
    `t`, not completed at `t'`, scheduled at `t'`, at related instants. `t.+1` is related to Lean's `t + 1`, and
    `t <= t'` to `t ≤ t'`. `sched_nonpreemptive` is over `uni_schedule`, related by the same scheduler
    correspondence as `sched`.
- **No certificate uses its own source or target theorem.** Statement types are taken with `type of`.
- **Audit:** 11 certificates.
  - 7 are `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 4 are `CERTIFIED`;
  - `semantic_premises=[]` and `unexpected=[]`;
  - no statement-only dependency;
  - no source or target theorem dependency;
  - `sorryAx` does not occur in the export.
- **Allowlist.** The definitional-UIP list includes the adapters' SProp `True` inductives `SvcTrue` and `ArTrue`, as
  in the accepted `prio_aware.v` configuration.

### Attempts

- **Prepare attempt 1:** refused, because the module receives the rewrite-order flag → the spec opts in with
  `module_change`.
- **Prepare attempt 2:** passed. The certificates compiled unchanged on the first run, and `check` passed.
- **Publish attempt 1:** a local-variable shadowing in the pipeline's fingerprint check (below) → fixed.
- **Publish attempt 2:** the qualifier list lacked the own names printed qualified at the head → completed.
  `check` was re-run and `publish` passed.

### Pipeline changes made for this publication

- **The `Prosa-fei` gate.** It now applies only while the `Prosa-fei` directory exists. The user removed that
  directory from the working tree on 2026-10-01 and instructed "treat as if there is no such folder exists".
  While the directory exists, the gate is unchanged.
- **A local name in `fingerprint_matches`.** The `dependency_qualified_in_type` branch assigned a local list
  `inventory`, which shadowed the module-level `inventory()` used by the `own_qualified_in_type` rule. That raised
  `UnboundLocalError` for specs that use only the latter. The local list is renamed `closure_rows`; behaviour is
  otherwise identical.

## Formal acceptance

Coverage **355 / 357 files**, **2424 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
