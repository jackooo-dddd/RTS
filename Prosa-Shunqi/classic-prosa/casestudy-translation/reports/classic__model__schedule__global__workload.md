# Report: `classic/model/schedule/global/workload.v` (rank 32)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/global/workload.v` |
| sha256 | `e4da65ee23f4e94efc07a2d6687c383ee3bc339ed3603c5afc94397b7234aecf` |
| Lean module | `Prosa/Classic/Model/Schedule/Global/Workload.lean` (namespace `Prosa.Classic.Model.Schedule.Global.Workload`) |
| Tier / layer | S / 11 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (4 source → Lean, same names)

- `Definition` `Workload.service_of_task`
- `Definition` `Workload.workload`
- `Definition` `Workload.workload_joblist`
- `Lemma` `Workload.workload_eq_workload_joblist`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Workload of a task (Rocq module `Workload`).

Representation notes: `(job_task j' == tsk)` used as a number is
`(decide (job_task j' = tsk)).toNat` (MathComp's `nat_of_bool`);
`\sum_(cpu < num_cpus) F cpu` is `∑ cpu : Fin num_cpus, F cpu`;
`\sum_(j <- l) F j` is the accepted v0.6 `Prosa.Util.Sum.sumSeq l F`.
Binder lists follow the Rocq contract (`service_of_task` takes `cpu` although
its body does not use it, as in the source).

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
