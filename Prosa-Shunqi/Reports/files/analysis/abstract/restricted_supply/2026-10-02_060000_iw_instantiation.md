# analysis/abstract/restricted_supply/iw_instantiation.v — canonical translation report

First experiment timestamp: **2026-10-02 06:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/abstract/restricted_supply/iw_instantiation.v`; rank 267.
- Public declarations: **17**:
  - `cumulative_interference_split`, `cumulative_interfering_workload_split`, `cumulative_task_interference_split`, `cumulative_intra_interference_split`, `cumulative_iw_hep_eq_workload_of_ohep`;
  - `quiet_time_cl_implies_quiet_time_ab`, `quiet_time_ab_implies_quiet_time_cl`, `instantiated_quiet_time_equivalent_quiet_time`, `instantiated_busy_interval_prefix_equivalent_busy_interval_prefix`, `instantiated_busy_interval_equivalent_busy_interval`, `abstract_busy_interval_classic_quiet_time`, `abstract_busy_interval_classic_busy_interval_prefix`;
  - `not_interference_implies_scheduled`, `scheduled_implies_no_interference`, `instantiated_i_and_w_are_coherent_with_schedule`, `instantiated_interference_and_workload_consistent_with_sequential_tasks`, `instantiated_i_and_w_no_speculative_execution`.
- The source's `#[local]` instances `rs_jlfp_interference` and `rs_jlfp_interfering_workload`, and the `Local Lemma busy_implies_not_idle`, are not in the public inventory.
- Dependencies (all accepted): `analysis/abstract/IBF/supply_task.v`, `analysis/facts/busy_interval/service_inversion.v`, `analysis/facts/interference.v`.

## Translation

`Prosa/Analysis/Abstract/RestrictedSupply/IwInstantiation.lean`.
- Binders follow the elaborated types, with `∀ [..]` binders for instances quantified after a hypothesis.
- The two section-local instances are `@[reducible]` definitions of the same names, passed explicitly wherever the elaborated statements use them implicitly.
- Booleans added to naturals are counted by `Bool.toNat`, the source's `nat_of_bool` coercion.
- The JLDP policy of service inversion is the accepted `JLFP_to_JLDP` of the JLFP policy, as elaborated.
- The classical and abstract busy-interval notions are distinguished by namespace.
- The source's `fun=> [eta has_supply sched]` is `fun _ t => has_supply sched t`.

Proofs:
- **The cumulative splits.** Pointwise, the three disjuncts of the instantiated interference are mutually exclusive under a uniprocessor, fully-consuming model:
  - a blackout excludes service;
  - service inversion and another higher-or-equal-priority job's service exclude each other on a uniprocessor.
  
  The interval sums then split (`sumSeq` over `List.range'` turned into `Finset.Ico` sums).
- **The busy-interval equivalences.** Classical and abstract quiet times coincide:
  - A classical quiet time makes the cumulative interference equal the interfering workload: blackouts and service inversion cancel on both sides, and higher-or-equal-priority service equals the completed workload.
  - Conversely, equality of the cumulative quantities forces every higher-or-equal-priority job arrived before `t` to be complete.
  
  Prefixes and busy intervals follow by unfolding.
- **The I/IW correctness lemmas.**
  - Work conservation plus work-bearing readiness gives service to some job whenever there is supply and no interference. That job must be `j` itself, by case analysis on its priority.
  - Consistency with sequential tasks: the abstract busy interval is classical, so `t1` is a classical quiet time. Under `policy_respects_sequential_tasks`, every earlier job of the task has higher-or-equal priority and is complete at `t1`. The accepted `all_jobs_have_completed_equiv_workload_eq_service` then equates the task's workload and service before `t1`.
  - No speculative execution: by the two splits, the higher-or-equal-priority interference from time 0 is the service of those jobs (time 0 is a classical quiet time). That service is bounded by their workload (accepted `service_of_jobs_le_workload`).

Lean axioms: only the standard ones. The build contains no `sorry`.

## Source binding

Extract mode, module `RsIwInstantiationSemanticSource`:
- The two local instances are byte-identical helper blocks, and the 17 statements are the authoritative elaborated types.
- IBF/supply_task and service inversion are bound to the accepted extracted sources of the base closure (`IbfSupplyTaskSemanticSource`, `ServiceInversionPredSemanticSource`).
- The interference definitions are bound to the accepted `InterferenceSemanticSource`, and the classical busy interval to the accepted `BusyIntervalClassicalSemanticSource`.
- `model/schedule/work_conserving` and `analysis/definitions/work_bearing_readiness` are the accepted compiled pinned sources.
- All of these are `.vo` artifacts hash-checked against their manifests. Their shared dependencies are byte-identical with this closure (checked).
- The proof-only imports `facts/interference` and `facts/busy_interval/service_inversion` are dropped.

The two local instances are implicit in the elaborated statements, so recorded printer repairs make every use explicit. There are 10 repairs:
- cumulative and conditional interference;
- cumulative interfering workload;
- abstract quiet time, busy-interval prefix and busy interval;
- abstract work conservation;
- `interference`;
- sequential consistency;
- no speculative execution.

The statements print back to the evidence text, and the fingerprint matches (17/17).

Attempt 1 (`…_attempt1_service_inversion_import`, kept) failed at the source compile, because `service_inversion` was not in scope. The fix was to export the accepted `ServiceInversionPredSemanticSource` explicitly.

## Validation

- **Spec** `analysis_abstract_restricted_supply_iw_instantiation.json`; base run `analysis_abstract_ibf_supply_task_final`.
- **Oleans:** 13 accepted oleans from the busy-interval and interference closures (interference facts, service-inversion busy prefix, preemption time, priority-driven schedules, preemption facts, work-bearing readiness, priority inversion, the existence, HEP-at-PT, PI, PI-bound and service-inversion busy-interval facts) are hash-checked artifacts.
- **Export:** 145,833 lines. The export root is the accepted IBF/supply_task root merged with the accepted busy-interval service-inversion and interference-facts roots, plus the two local instances and the statements.
- **Chain:** the accepted IBF/supply_task chain, the accepted `IbfTaskFullHelpers.v` (introduced for `ideal/abstract_seq_rta.v`), and the accepted `ServiceInversionPredCorrespondence.v` and `InterferenceCorrespondence.v`. Each is re-bound to this export and compiles unchanged.

Certificate `RsIwInstantiationCorrespondence.v`. Processor states use the same accepted state relation as the restricted-supply certificates: the two-sided `SvcProcessorStateRel` together with the pointwise `supply_on` relation. From it, the preemption and supply family relations are built (`rsi_jsvc`, `rsi_sup`).

Covered in both directions:
- arrival sequences and schedules;
- JLFP policies, pointwise on Booleans;
- readiness instances on the statement's schedule pair (the accepted funext-free pair cover, replayed over this relation);
- jobs, tasks and instants.

The two local instances are related field by field:
- blackout, by the accepted supply certificate;
- service inversion of the JLDP view, by the accepted service-inversion definition certificate;
- higher-or-equal-priority interference and interfering workload, by the accepted interference certificate.

The abstract notions are the accepted abstract-definitions, abstract-RTA and IBF/task certificates, applied over these instance relations. `nonself_intra` is the accepted IBF/supply_task certificate. The classical quiet time, busy interval, work conservation, work-bearing readiness and schedule validity are related by replaying the accepted busy-interval existence helpers over this relation. No source or target theorem is used.

Audit: 17 principal certificates plus the helper lemmas, all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. The audit observed aliases of the already-allowed SProp `True`/`HEq` constants through `IFC.I.*` and `SIPC.I.*`; I added exactly those to the UIP allowlist.

## Formal acceptance

Coverage **231 / 357 files**, **1627 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
