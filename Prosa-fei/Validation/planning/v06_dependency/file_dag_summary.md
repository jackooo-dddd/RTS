# Prosa v0.6 File Dependency Summary

Pinned commit: `414e66760333eaa4ef78c685bcf53291c527a548`.

## Scope

All **357** `.v` files are present exactly once.

| Category | Files |
|---|---:|
| CORE_AGGREGATOR | 4 |
| CORE_PROSA | 325 |
| IMPLEMENTATION | 13 |
| IMPLEMENTATION_REFINEMENT | 14 |
| LIBRARY_EXAMPLE | 1 |

## Graph facts

- Internal file edges: **1359**.
- External require occurrences: **178** (24 distinct modules).
- File layers: **30**.
- File cycles: **0**; the machine-readable JSON retains SCCs and condensation edges.
- Longest file dependency chain: **30 nodes**.
- Public source declarations: **2439**.
- Declaration edges extracted: **4628**.
- Files with unresolved declaration reference extraction: **14** (the refinement build boundary).

## One longest file chain

`util/supremum.v` → `util/list.v` → `util/bigcat.v` → `util/all.v` → `behavior/job.v` → `behavior/arrival_sequence.v` → `behavior/schedule.v` → `behavior/service.v` → `behavior/ready.v` → `behavior/all.v` → `model/task/concept.v` → `model/task/arrivals.v` → `analysis/facts/behavior/arrivals.v` → `analysis/facts/model/scheduled.v` → `analysis/facts/behavior/service.v` → `analysis/facts/behavior/completion.v` → `analysis/definitions/busy_interval/classical.v` → `analysis/facts/busy_interval/quiet_time.v` → `analysis/facts/model/service_of_jobs.v` → `analysis/abstract/iw_auxiliary.v` → `analysis/abstract/busy_interval.v` → `analysis/abstract/lower_bound_on_service.v` → `analysis/abstract/abstract_rta.v` → `analysis/abstract/IBF/task.v` → `analysis/abstract/ideal/iw_instantiation.v` → `analysis/abstract/ideal/cumulative_bounds.v` → `results/rta/ideal/edf/bounded_pi.v` → `results/rta/ideal/edf/bounded_nps.v` → `implementation/refinements/EDF/fast_search_space.v` → `implementation/refinements/EDF/refinements.v`

## Derived subsystem edges

| Dependency subsystem | Dependent subsystem | Edges |
|---|---|---:|
| analysis | analysis | 369 |
| analysis | implementation | 24 |
| analysis | model | 6 |
| analysis | results | 445 |
| behavior | analysis | 12 |
| behavior | behavior | 11 |
| behavior | implementation | 2 |
| behavior | model | 21 |
| implementation | implementation | 39 |
| model | analysis | 163 |
| model | implementation | 10 |
| model | model | 63 |
| model | results | 73 |
| results | implementation | 2 |
| results | results | 12 |
| util | analysis | 29 |
| util | behavior | 2 |
| util | implementation | 4 |
| util | model | 16 |
| util | results | 8 |
| util | util | 48 |

## Highest file fan-out (transitive dependents)

| File | Layer | Transitive dependents |
|---|---:|---:|
| `util/tactics.v` | 0 | 346 |
| `util/supremum.v` | 0 | 340 |
| `util/list.v` | 1 | 339 |
| `util/nat.v` | 1 | 339 |
| `util/notation.v` | 0 | 338 |
| `util/rel.v` | 0 | 337 |
| `util/setoid.v` | 0 | 335 |
| `util/epsilon.v` | 0 | 334 |
| `util/minmax.v` | 2 | 334 |
| `util/subadditivity.v` | 0 | 334 |
| `util/bigcat.v` | 2 | 333 |
| `util/bigop.v` | 0 | 333 |
| `util/div_mod.v` | 2 | 333 |
| `util/nondecreasing.v` | 2 | 333 |
| `util/poet.v` | 2 | 333 |
| `util/search_arg.v` | 1 | 333 |
| `util/seqset.v` | 0 | 333 |
| `util/sum.v` | 2 | 333 |
| `util/unit_growth.v` | 1 | 333 |
| `behavior/time.v` | 0 | 332 |
| `util/all.v` | 3 | 332 |
| `behavior/job.v` | 4 | 328 |
| `behavior/arrival_sequence.v` | 5 | 326 |
| `behavior/schedule.v` | 6 | 325 |
| `behavior/service.v` | 7 | 319 |
| `behavior/ready.v` | 8 | 315 |
| `behavior/all.v` | 9 | 313 |
| `model/task/concept.v` | 10 | 290 |
| `model/task/arrivals.v` | 11 | 241 |
| `model/priority/definitions.v` | 11 | 225 |

## Highest declaration fan-out

| Declaration | Kind | Transitive dependents | Extraction |
|---|---|---:|---|
| `prosa.behavior.job.JobType` | Definition | 1403 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.time.instant` | Definition | 1370 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.job.work` | Definition | 1206 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.schedule.ProcessorState` | Class | 915 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.arrival_sequence.arrivals_at` | Definition | 779 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.model.task.concept.TaskType` | Definition | 774 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.schedule.service_in` | Definition | 684 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.service.service_at` | Definition | 669 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.time.duration` | Definition | 643 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.job.JobCost` | Class | 556 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.service.service_during` | Definition | 553 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.job.JobArrival` | Class | 535 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.arrival_sequence.arrivals_between` | Definition | 497 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.service.service` | Definition | 475 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.model.task.concept.JobTask` | Class | 452 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.schedule.scheduled_in` | Definition | 397 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.service.scheduled_at` | Definition | 386 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.service.completed_by` | Definition | 358 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.arrival_sequence.arrives_in` | Definition | 348 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.model.task.concept.job_of_task` | Definition | 300 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.arrival_sequence.arrivals_up_to` | Definition | 277 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.model.task.arrival.curves.MaxArrivals` | Class | 254 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.model.priority.definitions.JLFP_policy` | Class | 249 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.model.task.concept.TaskCost` | Class | 243 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.schedule.schedule` | Definition | 187 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.model.priority.definitions.FP_policy` | Class | 186 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.analysis.definitions.request_bound_function.task_request_bound_function` | Definition | 184 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.model.schedule.scheduled.scheduled_jobs_at` | Definition | 150 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.arrival_sequence.has_arrived` | Definition | 138 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |
| `prosa.behavior.service.pending` | Definition | 124 | VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES |

## Interpretation

Layers and priority rankings are graph-derived. A lower layer is not automatically semantically more important; transitive dependent count identifies representation choices with broad downstream impact.
The declaration graph is intentionally not a Lean-proof translation order: theorem proof-body references are excluded.
Declaration edges establish explicit `.glob` references and mapped generated symbols only. Absence of an edge does not establish absence of an implicit typeclass/canonical/HB dependency; the file DAG remains authoritative for readiness.
