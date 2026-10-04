# Report: `classic/model/schedule/apa/interference.v` (rank 33)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/apa/interference.v` |
| sha256 | `966dcb65ab81d4377ded376ac79496517598e5b5a1c4e86566aab7d9daeeef93` |
| Lean module | `Prosa/Classic/Model/Schedule/Apa/Interference.lean` (namespace `Prosa.Classic.Model.Schedule.Apa.Interference`) |
| Tier / layer | S / 12 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (11 source → Lean, same names)

- `Definition` `Interference.higher_priority_task_in`
- `Definition` `Interference.different_task_in`
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

Interference under processor affinities (APA; Rocq module `Interference` of
`classic/model/schedule/apa`).  As the global version, plus the affinity
condition `can_execute_on alpha (job_task j) cpu` in each per-processor term
(`a && b && c` is `(a && b) && c`).

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
