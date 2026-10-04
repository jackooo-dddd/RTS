# Report: `classic/model/schedule/global/basic/interference.v` (rank 34)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/global/basic/interference.v` |
| sha256 | `fd7dde9e3e437a793cb4f050a4c547ed75613a21475b26427a745f434f2290e9` |
| Lean module | `Prosa/Classic/Model/Schedule/Global/Basic/Interference.lean` (namespace `Prosa.Classic.Model.Schedule.Global.Basic.Interference`) |
| Tier / layer | S / 12 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (9 source → Lean, same names)

- `Definition` `Interference.total_interference`
- `Definition` `Interference.job_interference`
- `Definition` `Interference.task_interference`
- `Definition` `Interference.task_interference_joblist`
- `Lemma` `Interference.total_interference_le_delta`
- `Lemma` `Interference.job_interference_le_service`
- `Lemma` `Interference.task_interference_le_workload`
- `Lemma` `Interference.job_interference_le_delta`
- `Lemma` `Interference.interference_le_interference_joblist`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `service_at_eq_sum`.

## Representation notes

Interference in global schedules (Rocq module `Interference`).

Representation notes: a Boolean summed as a number (MathComp `nat_of_bool`) is
`Bool.toNat`; `\sum_(t1 <= t < t2)` is `∑ t ∈ Finset.Ico t1 t2`;
`\sum_(cpu < num_cpus)` is `∑ cpu : Fin num_cpus`; the filtered list sum
`\sum_(j <- l | P j) F j` is the v0.6 `Prosa.Util.Sum.sumFiltered l P F`.  The
section-local `job_is_backlogged t := backlogged job_arrival job_cost sched j t`
is unfolded.  Binder lists follow the Rocq contract.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
