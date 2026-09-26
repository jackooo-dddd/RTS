# implementation/definitions/ideal_uni_scheduler.v — canonical translation report

First experiment timestamp: **2026-09-30 16:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/definitions/ideal_uni_scheduler.v`.
- Public declarations: **5**, all computational definitions: `prev_job_nonpreemptive`, `allocation_at`, `pmc_uni_schedule`, `choose_highest_prio_job`, `uni_schedule`.
- Dependencies (generic scheduler, ideal processor, preemption parameter, work-conserving backlog, priority classes, `util/supremum`): accepted.

## Translation

`Prosa/Implementation/Definitions/IdealUniScheduler.lean`. Conventions:
- The section-local `PState` is the accepted ideal processor `processor_state Job`, and the idle state is `none`.
- The Boolean `if` is `bif`; `if e is Some j then … else …` is a `match`; `~~ b` is `!b`; `t.-1` is `t - 1`.
- The readiness model, preemption model and JLDP policy are instance binders, as in the source `Context`.

Lean axioms: none beyond the standard ones.

## Source binding

The five definitions are extracted as byte-identical blocks (module `IdealUniSchedulerSemanticSource`).
- Pinned sources compiled from the tree: `schedule_prefix`, `sequentiality`, `swap`, `ideal`, `generic_scheduler`, `work_conserving`. `schedule_prefix` and `ideal` use their accepted proof-only compatibility patches.
- The readiness source is the accepted extracted `ReadinessSemanticSource`, hash-checked as an extra artifact.
- The section variables `sched_prefix`/`t`, `arr_seq`/`choose_job` and `arr_seq` are reconnected by recorded local notations for `prev_job_nonpreemptive`, `allocation_at` and `pmc_uni_schedule`.

All 5 declarations match the evidence (fingerprint: 5 checked, 0 mismatches).

## Validation

Spec `implementation_definitions_ideal_uni_scheduler.json`; base run `analysis_transform_prefix_final`.

Export: 148,524 lines, 113 targets, 39 body theorems. The export root:
- is the accepted transform-prefix root;
- adds the ideal processor, the generic scheduler, `replace_at`, the work-conserving backlog, `supremum` and the five definitions;
- adds kernel-checked Lean equations at the ideal processor: `schedule_up_to` (zero/successor), `empty_schedule`, `replace_at` (same/other instant), and the ideal `scheduled_in`/`service_in`.

Attempts:
- `attempt1`: the readiness source was unbound.
- `attempt2`: `schedule_prefix` was unbound.
- `attempt3`: the `schedule_prefix` patch was missing.
- `attempt4`: the `prev_job_nonpreemptive` local binding was missing.
- `attempt5`: the ideal-state equations were missing from the fixture. I stopped this prepare run myself.

All five runs were archived. The final run passed.

Certificate chain:
- The accepted ArrivalsSeq*/JitterSvc*/PreemptionParameter certificates, re-bound.
- The new `IdealUniSchedulerCorrespondence.v`:
  - States are related by the constructor-preserving Option map, and schedules pointwise.
  - `job_cost` is related by `SvcJobCostRel`, `job_arrival` by `ArJobArrivalRel`, and the arrival sequence by `ArArrivalSequenceRel`.
  - `job_ready` is related on related schedules and instants. The preemption model and JLDP policy are related pointwise. `choose_job` is related on related instants and job lists.
  - `service` is closed by the accepted interval-sum certificate.
  - The backlog is closed by the accepted filter and `arrivals_up_to` certificates.
  - `schedule_up_to` and `replace_at` are closed by induction and case analysis with the exported equations. `supremum` is closed by list induction.
  - Lean matchers are related by transporting their scrutinee.
  - No source or target theorem is used.

Audit: 5 principal certificates, all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`.

## Formal acceptance

Coverage **191 / 357 files**, **1345 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
