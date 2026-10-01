# implementation/refinements/FP/preemptive_sched.v — canonical translation report

First experiment timestamp: **2026-10-07 22:00:00 +08:00**

The thirteenth file behind the CoqEAL build boundary. The inventory places it there, so its type evidence is the
official-toolchain CoqEAL evidence, as for `refinements.v`. The file itself does not use CoqEAL: its closure
contains no CoqEAL module.

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/refinements/FP/preemptive_sched.v`; layer 20; rank 351.
- **6 public declarations:**
  - the section's aliases `Task` and `Job`;
  - the `Instance sequential_ready_instance` (over the section's `arr_seq`);
  - the definition `sched`;
  - the `Remark sched_valid` and the `Lemma respects_policy_at_preemption_point`.
- **Dependencies (accepted):** `analysis/definitions/tardiness.v`, `analysis/facts/preemption/rtc_threshold/preemptive.v`,
  `analysis/facts/preemption/task/preemptive.v`, `analysis/facts/readiness/sequential.v`,
  `implementation/definitions/task.v`, `implementation/facts/ideal_uni/prio_aware.v`.

## Translation

`Prosa/Implementation/Refinements/FP/PreemptiveSched.lean` compiles with only the standard Lean axioms.

- **Aliases.** `Task` and `Job` (the concrete types as `eqType`s) are abbreviations of the accepted concrete types.
- **Instances.**
  - The source's section `Instance sequential_ready_instance` (over `arr_seq`) is a named definition taking
    `arr_seq`. It is the accepted `sequential_ready_instance` with `Task` explicit, as in the accepted
    `Sequential.lean` (`Task`/`arr_seq` are not inferable).
  - The section-local instances are passed explicitly to `uni_schedule`: this readiness model,
    `fully_preemptive_job_model`, and `NumericFPAscending Task` through the FP-to-JLFP and JLDP coercions (the
    source's file-wide `#[local] Existing Instance NumericFPAscending`).
- **Binders.** The section's `arr_seq` and `H_valid_arrivals` are explicit binders, in the order of the elaborated
  types. `sched_valid` does not take `H_valid_arrivals`: its elaborated type does not.
- **Proofs** follow the source: the accepted `uni_schedule_valid` and `schedule_respects_policy`, with the accepted
  sequential-readiness nonclairvoyance.

## Source binding

Source mode `official_closure`, with the run's CoqEAL build.
- **Closure:** `Validation/tooling/proof_closure/refinements_FP_preemptive_sched_closure.txt`.
- **Patch:** `…-refinements-FP_preemptive_sched.patch`, proof-only. The module itself is compiled byte-identically.

### Type fingerprints

6/6 are `EXACT_MODULO_OWN_MODULE_QUALIFIER`. The official evidence context loads the four `*_sched.v` files,
which declare the same short names, so it prints this file's own names qualified by their module
(`preemptive_sched.Job`, `preemptive_sched.Task`, `…sched`), both at the head and inside the types. Exactly those names are listed in the spec's
`own_qualified_in_type`.

## Validation

- **Spec:** `implementation_refinements_FP_preemptive_sched.json`.
- **Lean base run:** `implementation_refinements_EDF_nonpreemptive_sched_final`, with the accepted oleans of the scheduler
  closure (each checked against its accepted manifest).
- **Export:** 155,894 lines. Its root is the file's 4 definitions with bodies and its 2 statements statement-only,
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
- **`RefFPPSchedCorrespondence.v` (new).**
  - Principal totals for `Task` and `Job`.
  - Sequential readiness, for related arrival sequences: `pending` and the completion of the earlier jobs of the
    same task. That is `all` over `task_arrivals_before` (a `filter` of `job_of_task`, task equality through the
    accepted `it_task_decide_related`).
  - The fully-preemptive model: always preemptable on both sides.
  - `NumericFPAscending`: the comparison of the task priorities of the jobs' tasks.
  - `sched`, for related arrival sequences.
  - The two statements.
- **No certificate uses its own source or target theorem.** Statement types are taken with `type of`.
- **Audit:** 8 certificates.
  - 4 are `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 4 are `CERTIFIED`;
  - `semantic_premises=[]` and `unexpected=[]`;
  - no statement-only dependency;
  - no source or target theorem dependency;
  - `sorryAx` does not occur in the export.
- **Allowlist.** The definitional-UIP list includes the adapters' SProp `True` inductives `SvcTrue` and `ArTrue`, as
  in the accepted `prio_aware.v` configuration.

### Attempts

- **Prepare attempt 1:** passed. The certificates compiled on the first run, and `check` and `publish` passed.

### Pipeline changes made for this publication

- **The `Prosa-fei` gate.** It now applies only while the `Prosa-fei` directory exists. The user removed that
  directory from the working tree on 2026-10-01 and instructed "treat as if there is no such folder exists".
  While the directory exists, the gate is unchanged.
- **A local name in `fingerprint_matches`.** The `dependency_qualified_in_type` branch assigned a local list
  `inventory`, which shadowed the module-level `inventory()` used by the `own_qualified_in_type` rule. That raised
  `UnboundLocalError` for specs that use only the latter. The local list is renamed `closure_rows`; behaviour is
  otherwise identical.

## Formal acceptance

Coverage **356 / 357 files**, **2430 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
