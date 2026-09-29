# results/rta/arm/fp/fully_nonpreemptive.v — canonical translation report

First experiment timestamp: **2026-10-03 17:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/arm/fp/fully_nonpreemptive.v`; rank 316.
- Public declarations: **3**:
  - the definitions `busy_window_recurrence_solution` and `rta_recurrence_solution`;
  - the theorem `uniprocessor_response_time_bound_fully_non_preemptive_fp`.
- Dependencies (all accepted): `analysis/abstract/restricted_supply/bounded_bi/fp.v`, `analysis/abstract/restricted_supply/search_space/fp.v`, `analysis/abstract/restricted_supply/task_intra_interference_bound.v`, `analysis/facts/model/sbf/average.v`, `analysis/facts/preemption/rtc_threshold/nonpreemptive.v`, `analysis/facts/preemption/task/nonpreemptive.v`, `analysis/facts/readiness/basic.v`, `model/composite/valid_task_arrival_sequence.v`.

## Translation

`Prosa/Results/Rta/Arm/Fp/FullyNonpreemptive.lean`.
- **The two definitions:** the recurrences of the accepted restricted-supply result `results/rta/rs/fp/fully_nonpreemptive.v`, with the supply bound
  function instantiated by the average resource model SBF `arm_sbf Π Θ ν`; the parameters (Π, Θ, ν) are explicit arguments
  (`Π` cannot be a Lean binder name and is spelled `Pi`).
- **The theorem:** under the average resource model (Π, Θ, ν), any solution `R` bounds the response times of `tsk` under FP
  scheduling with fully non-preemptive jobs and tasks (a non-preemptive schedule) and basic readiness on a uniprocessor. The proof instantiates the accepted restricted-supply
  analysis with the resource-model SBF, which is monotone, unit-slope and a valid busy SBF by the accepted
  average-resource-model facts.

Binders follow the elaborated source types and the source's binder order, including where the processor model is quantified.
The section-local instances are passed explicitly where the elaborated statement uses them implicitly. Lean axioms: only the standard ones.

## Source binding

Extract mode, module `RtaArmFpFullyNonpreemptiveSemanticSource`.
- The two definitions are byte-identical computational blocks, and the theorem statement is the authoritative elaborated type (proof omitted).
- The accepted extracted sources of the restricted-supply result are bound as hash-checked `.vo` artifacts;
  `util/setoid`, `analysis/definitions/sbf/sbf`, `analysis/definitions/sbf/pred`, `model/preemption/fully_nonpreemptive`, `model/schedule/nonpreemptive`, `analysis/definitions/sbf/plain`, `analysis/definitions/sbf/average`, `model/composite/valid_task_arrival_sequence` are compiled from the pinned tree (the SBF files
  under their accepted Rocq 9.3 compatibility patches).
- The proof-only imports of the official file are dropped.
- Recorded printer repairs make the instances implicit in the elaborated statement explicit, following the official
  `Set Printing All` print, and map the own-module qualifier `arm.fp.fully_nonpreemptive.X` to `X`.
- **Implicit-instance check:** the extracted statement was printed with `Set Printing All` and compared with the official
  print; they are identical up to display qualifiers.

The fingerprints match (3/3).

## Validation

- **Spec** `results_rta_arm_fp_fully_nonpreemptive.json`; base run `analysis_abstract_restricted_supply_bounded_bi_fp_final`.
- **Oleans:** the accepted oleans of the closure are hash-checked artifacts. 55 of 56 fixture oleans were reused from the verified content-addressed cache.
- **Export:** 147,096 lines. The export root is the export root of `results/rta/rs/fp/fully_nonpreemptive.v`, merged with the accepted
  average-resource-model SBF facts root, plus the two definitions and the statement.
- **Chain:** the chain of `results/rta/rs/fp/fully_nonpreemptive.v`, the accepted average-resource-model SBF chain, and `AverageCorrespondence`, `RsPStateCover`
  before the main certificate.

Attempts:
- **Finalization attempt 0** (`rtaarmfpfnp_final_attempt0_theorem_name_spelling.log`) stopped in the finalizer's own consistency check, before any pipeline stage. The generated certificate named the theorem with the restricted-supply spelling `…_fully_nonpreemptive_fp` instead of this file's source spelling `…_fully_non_preemptive_fp`. The certificate generator was corrected and the certificate regenerated.
- **Finalization attempt 1:** accepted; the chain compiled on the first check, and the recheck after pruning reused it from its checkpoints. The helper aliases this run observed were already in the UIP allowlist.

Certificate `RtaArmFpFullyNonpreemptiveCorrespondence.v`, derived by the certificate generator from the accepted certificate of `results/rta/rs/fp/fully_nonpreemptive.v` with
the resource-model delta of the accepted ARM FP fully preemptive certificate. Before the first check, three static checks
passed: chain references, lemma signatures and binder names. Leading inputs are those of the restricted-supply certificate without the processor state:
- task_cost pointwise, max_arrivals by the accepted CvMaxArrivalsRel, job_task by the accepted AdJobTaskRel, job_arrival pointwise, job_cost pointwise.

Covered in both directions: FP policies, task sets, arrival sequences, schedules, tasks, durations, instants, resource-model parameters (Π, Θ, ν); the processor model, quantified inside the statement, covered in both directions by rs_forall_pstate (the accepted two-sided SvcProcessorStateRel with the pointwise supply_on relation).

What differs from the restricted-supply certificate:
- **The processor model:** quantified inside the statement and covered in both directions by `rs_forall_pstate`
  (`RsPStateCover.v`: the accepted two-sided `SvcProcessorStateRel` with the pointwise `supply_on` relation). The
  schedule-level relations are instantiated at each related processor-model pair.
- **Readiness:** the basic readiness model, related from the accepted pending relation; `sequential_tasks` by the accepted certificate.
- **`valid_task_arrival_sequence`:** by unfolding into the accepted arrival-sequence, job-cost, task-set and arrival-curve relations.
- **The average resource model and `arm_sbf Π Θ ν`:** the accepted certificates over the supply view of the processor relation, in place
  of the supply bound function.

All other relations are those of the restricted-supply certificate. No source or target theorem is used.

Audit: 17 certificates (the two definitions, the statement and the helper lemmas), all certified, with
`semantic_premises=[]` and `unexpected_assumptions=[]`. The statement certificate's assumptions include those of the
processor-model cover (standard foundation only). `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **266 / 357 files**, **1748 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
