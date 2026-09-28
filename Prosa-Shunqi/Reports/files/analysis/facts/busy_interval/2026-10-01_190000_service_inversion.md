# analysis/facts/busy_interval/service_inversion.v — canonical translation report

First experiment timestamp: **2026-10-01 19:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/facts/busy_interval/service_inversion.v`; rank 228.
- Public declarations: **12**:
  - `blackout_implies_no_service_inversion`, `idle_implies_no_service_inversion`, `receives_service_implies_no_service_inversion`
  - `service_inversion_cat`, `service_inversion_widen`, `service_inversion_supply_sched`
  - `service_inv_implies_priority_inv`, `cumul_service_inv_le_cumul_priority_inv`
  - `cumulative_service_inversion_from_one_job`, `lp_job_bounded_service`, `lp_job_bounded_service_max`
  - `service_inversion_is_bounded`
- Dependencies (both accepted): `analysis/definitions/service_inversion/busy_prefix.v`, `analysis/facts/busy_interval/pi.v`.

## Translation

`Prosa/Analysis/Facts/BusyInterval/ServiceInversion.lean`.

Binders follow the elaborated types. Each lemma takes only the section inputs and hypotheses it uses, in their elaborated order. Where the source applies the JLDP-based service inversion to a JLFP policy, the policy goes through the accepted `JLFP_to_JLDP`, passed explicitly.

Proofs follow the source:
- **Basic lemmas:** from the witness of a service inversion (a served lower-priority job while `j` is not served). The uniprocessor and supply facts rule out the blackout, idle and self-service cases.
- **`cumulative_service_inversion_from_one_job`:** the positive sum exhibits a served lower-priority job `jlp`. It arrived before the prefix (the accepted `low_priority_job_arrives_before_busy_interval_prefix`). At every instant, unit supply splits into two cases:
  - service 0: the accepted `only_one_pi_job` excludes another inverting job;
  - service 1: `jlp` is the served lower-priority job.
- **`lp_job_bounded_service`:** a preemption point `σ` within `job_max_nonpreemptive_segment - 1` of the service at `t1`, taken from the bounded-segment model. If the service passes `σ` strictly, then either:
  - `t1` is a preemption time with `jlp` scheduled, excluded by the accepted `lower_priority_job_scheduled_implies_no_preemption_time`; or
  - the `σ`-th scheduling instant is a preemption time at which the lower-priority `jlp` is scheduled, excluded by the accepted `scheduled_at_preemption_time_implies_higher_or_equal_priority`.
- **`lp_job_bounded_service_max`:** `jlp` is a term of the conditional maximum.
- **`service_inversion_is_bounded`:** through the accepted `busy_interval_pi_cases` and `preemption_time_interval_case`. A private helper bounds the cumulative service inversion over an interval without preemption times by the service of a job scheduled in it.

Lean axioms: only the standard ones. The build contains no `sorry`.

## Source binding

Module `BusyIntervalServiceInversionSemanticSource`: the statements are the authoritative elaborated types (proofs omitted). The following are bound to accepted extracted sources:
- service inversion and its cumulative sum: `ServiceInversionPredSemanticSource`;
- the busy-prefix bound: `ServiceInversionBusyPrefixSemanticSource`, whose compiled dependencies are byte-identical to this closure's;
- `max_lp_nonpreemptive_segment`: the `pi` source;
- the task preemption parameters.

The fingerprint matches for all 12 statements.

## Validation

Spec `analysis_facts_busy_interval_service_inversion.json`; base run `analysis_facts_busy_interval_pi_bound_final`.

Export: 141,363 lines. The export root merges the accepted `pi_bound` root with the accepted service-inversion busy-prefix root: the union of their targets, body projections and kernel guards, over the same preemption-parameter closure. This is needed so that both accepted certificate chains apply.

Certificate `BusyIntervalServiceInversionCorrespondence.v`, over the accepted pi chain plus the accepted `ServiceInversionPredCorrespondence.v`, rebound to this artifact:
- **Leading inputs** (related): `JobArrival`, `JobCost`, `TaskMaxNonpreemptiveSegment`, `JobTask`.
- **Covers:** every other input through the accepted covers (processor models, arrival sequences, schedules, JLFP policies, `JobPreemptable`, `JobReady` at the statement's schedule pair, blocking-bound functions, tasks, jobs, instants).
- **New cover:** JLDP policies are covered pointwise on Booleans at related instants (`bsi_forall_jldp`), in the same way as the accepted JLFP cover.
- **Service inversion:**
  - replayed over the processor-model pair observations;
  - the `List.any` and bool-to-nat lemmas of the accepted definition certificate are reused;
  - the interval sum goes through the accepted `svc_interval_sum_related` against the kernel-guarded projection.
- **Supply:** `supply_at`/`has_supply`/`is_blackout`, unit supply and full consumption are related through the processor-model relation's `supply_in` component.

Audit: 12 principal certificates, all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`.

## Formal acceptance

Coverage **218 / 357 files**, **1518 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
