# results/rta/arm/fp/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-03 12:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/arm/fp/fully_preemptive.v`; rank 317.
- Public declarations: **3**:
  - the definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - the theorem `uniprocessor_response_time_bound_fully_preemptive_fp`.
- Dependencies (all accepted): `analysis/abstract/restricted_supply/bounded_bi/fp.v`, `analysis/abstract/restricted_supply/search_space/fp.v`, `analysis/abstract/restricted_supply/task_intra_interference_bound.v`, `analysis/facts/model/sbf/average.v`, `analysis/facts/preemption/rtc_threshold/preemptive.v`, `analysis/facts/preemption/task/preemptive.v`, `analysis/facts/readiness/basic.v`, `model/composite/valid_task_arrival_sequence.v`.

## Translation

`Prosa/Results/Rta/Arm/Fp/FullyPreemptive.lean`.
- **The two definitions:** the restricted-supply FP recurrences, with the supply bound function instantiated by the average-resource-model SBF `arm_sbf Π Θ ν`:
  - the busy-window recurrence: `0 < L ∧ total_hep_rbf L ≤ arm_sbf Π Θ ν L`;
  - the response-time recurrence: for every `A` in the FP search space, some `F ≤ A + R` with `task_rbf (A + 1) + total_ohep_rbf F ≤ arm_sbf Π Θ ν F`.
- **The theorem:** under the average resource model `(Π, Θ, ν)`, any solution `R` bounds the response times of `tsk` under fully preemptive FP scheduling with sequential tasks and basic readiness on a uniprocessor. The proof instantiates the accepted restricted-supply analysis with `arm_sbf` as the SBF: it is monotone, unit-slope and a valid busy SBF, by the accepted average-resource-model facts. The FP blocking bound vanishes in the fully preemptive task model.
- `Π` cannot be a Lean binder name; it is spelled `Pi`.

Binders and representation:
- Binders follow the elaborated source types, including the source's binder order (task set and task before the processor model).
- `basic_ready_instance` and the fully preemptive job model are passed explicitly where the elaborated statement uses them implicitly.
- `ε` is `1`.

Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaArmFpFullyPreemptiveSemanticSource`.
- The two definitions are byte-identical computational blocks, and the theorem statement is the authoritative elaborated type (proof omitted).
- **Bound to accepted extracted sources**, whose `.vo` files are hash-checked against their manifests: the same restricted-supply FP sources as the accepted RS fully preemptive FP result.
- `model/preemption/fully_preemptive`, `model/composite/valid_task_arrival_sequence`, `analysis/definitions/sbf/{sbf,pred,plain,average}` and `util/setoid` are compiled from the pinned tree (the SBF files under their accepted Rocq 9.3 compatibility patches); `model/readiness/basic` and `model/task/sequentiality` come from the base source tree.
- The proof-only facts imports are dropped.
- Recorded printer repairs:
  - make the readiness, job-preemption-model and FP-policy instances explicit, following the official `Set Printing All` print;
  - map the own-module qualifier `arm.fp.fully_preemptive.X` to `X`.
- **Implicit-instance check:** the extracted statement was printed with `Set Printing All` and compared with the official print; they are identical up to display qualifiers.

The fingerprints match (3/3).

## Validation

- **Spec** `results_rta_arm_fp_fully_preemptive.json`; base run `analysis_abstract_restricted_supply_bounded_bi_fp_final`.
- **Oleans:** the accepted oleans of the closure are hash-checked artifacts. 53 of 56 fixture oleans were reused from the verified content-addressed cache; the three average-resource-model fixtures were built fresh.
- **Export:** 146,974 lines. The export root is the accepted RS fully preemptive FP export root, merged with the accepted average-resource-model SBF facts root, plus the two definitions and the statement.
- **Chain:** the accepted RS fully preemptive FP chain, the accepted average-resource-model SBF chain, and `RsPStateCover` before the main certificate.

Attempts:
- **Finalization attempt 1** (`rtaarmfpfp_final_attempt1_vtas_arg_order.log`): the 70-module chain prefix, including `RsPStateCover`, compiled. The main certificate stated the `valid_task_arrival_sequence` relation with the job-arrival and job-cost instances swapped. The elaborated order, both in the official `Set Printing All` print and in the Lean definition, is job task, job cost, job arrival. The argument order was corrected here and in the PRM and EDF drafts sharing this lemma.
- **Finalization attempt 2** (`rtaarmfpfp_final_attempt2_alias_allowlist.log`) stopped at the assumption audit on the helper aliases `RsPStateCover`/`SEQC.I.{True,HEq,HEq_inst1}`, which were added to the UIP allowlist. No other assumption was reported.
- Each re-check reused the compiled chain prefix from its checkpoints (70, then all 72 modules).

**Processor-model cover (`RsPStateCover.v`).** Unlike the RS results, the ARM statement quantifies over the processor model inside the statement. So the certificate needs a two-way cover of processor models in the accepted restricted-supply relation family (`SvcProcessorStateRel` with the pointwise `supply_on` relation):
- **Rocq → Lean:** a Lean processor model over the Rocq state type, with a finite core type built by `fintypeOfNodupListing`. Its choice-based core enumeration is a permutation of the Rocq enumeration, and the fields are read back through that permutation.
- **Lean → Rocq:** a finite type built from the Lean core enumeration list, giving the exact enumeration equality.
- `Print Assumptions` of the cover lemma shows only the standard foundation.

Certificate `RtaArmFpFullyPreemptiveCorrespondence.v`. Leading inputs:
- `task_cost`, `job_cost` and `job_arrival` pointwise;
- `max_arrivals` by the accepted `CvMaxArrivalsRel`;
- `job_task` by the accepted `AdJobTaskRel`.

Covered in both directions: task sets, tasks, FP policies, arrival sequences, schedules, resource-model parameters and instants; the processor model by `rs_forall_pstate`.

What is related, and how:
- **The basic readiness model:** at each related schedule pair, from the accepted pending relation.
- **The fully preemptive job and task models:** pointwise.
- **`valid_task_arrival_sequence`:** by unfolding into the accepted arrival-sequence, job-cost, task-set and arrival-curve relations.
- **`sequential_tasks`:** the accepted certificate.
- **The average resource model and `arm_sbf`:** the accepted certificates, over the supply view of the processor relation.
- **Schedule validity, work conservation, the FP policy at preemption points, the FP search space, the RBFs and the task response-time bound:** related as in the accepted RS fully preemptive FP certificate.

No source or target theorem is used.

Audit: 15 certificates (the two definitions, the statement and the helper lemmas), all certified, with `semantic_premises=[]` and `unexpected_assumptions=[]`. The statement certificate's assumptions include those of the processor-model cover, which are the standard foundation only. `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **261 / 357 files**, **1733 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
