# analysis/definitions/work_bearing_readiness.v — canonical translation report

First experiment timestamp: **2026-09-26 16:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `analysis/definitions/work_bearing_readiness.v`; layer 14;
  execution rank 101. Public declarations: **1** (`work_bearing_readiness`).
  Dependency `model/priority/classes.v` accepted.

## Translation

`Prosa/Analysis/Definitions/WorkBearingReadiness.lean` (noncomputable, as
`pending`): for every arrived job `j` and time `t`, `pending sched j t = true`
implies `∃ j_hp, arrives_in arr_seq j_hp ∧ job_ready sched j_hp t = true ∧ hep_job j_hp j = true`.
Binder order follows the elaborated source (`Job, JobArrival, JobCost, PState,
JobReady, arr_seq, sched, JLFP`). Lean axioms: `propext`, `Classical.choice`, `Quot.sound`.

## Validation

Spec `analysis_definitions_work_bearing_readiness.json`; pinned source
byte-identical; fingerprint `EXACT_HASH`. Export root
`WorkBearingReadinessComputationInterface` (definition, JLFP policy class and
the accepted ArrivalSequence and Service/Schedule interfaces): 124,810 lines
(over 100k, diagnosed: accepted Service/Schedule closure). Certificates: the
accepted ArrivalsSeq* / JitterSvc* chains re-bound to
`ImportedWorkBearingReadiness`, and `work_bearing_readiness_correspondence`.
Input relations: job arrival/cost, two-sided processor state/schedule, the
JobReady instance related on its operation for every related schedule (the
accepted `RdyJobReadyRel` design of behavior/ready), arrival sequence, and the
JLFP policy (`WbJLFPRel`, with two-way totals `JLFP_policy_source_total` /
`_target_total`). Existential witnesses are jobs (identity carrier). Audit:
5 certificates `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`, `semantic_premises=[]`.

## Formal acceptance

Coverage **100 / 357 files**, **712 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
