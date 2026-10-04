# Report: `classic/model/arrival/basic/task.v` (rank 22)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/arrival/basic/task.v` |
| sha256 | `7c9adc9a3cc480894cac0948145570afc368c796526c44beb1ed2ef2eb2c7691` |
| Lean module | `Prosa/Classic/Model/Arrival/Basic/Task.lean` (namespace `Prosa.Classic.Model.Arrival.Basic.Task`) |
| Tier / layer | S / 6 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (11 source → Lean, same names)

- `Definition` `SporadicTask.task_cost_positive`
- `Definition` `SporadicTask.task_period_positive`
- `Definition` `SporadicTask.task_deadline_positive`
- `Definition` `SporadicTask.task_cost_le_deadline`
- `Definition` `SporadicTask.task_cost_le_period`
- `Definition` `SporadicTask.is_valid_sporadic_task`
- `Definition` `SporadicTaskset.taskset_of`
- `Definition` `SporadicTaskset.valid_sporadic_taskset`
- `Definition` `SporadicTaskset.implicit_deadline_model`
- `Definition` `SporadicTaskset.constrained_deadline_model`
- `Definition` `SporadicTaskset.arbitrary_deadline_model`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Attributes of valid sporadic tasks and task sets.

Representation notes (classic representation rules, see the plan README):
* `Context {Task : eqType}` is an implicit carrier `{Task}` with
  `[DecidableEq Task]`; model parameters such as `task_cost : Task → time` stay
  explicit function arguments, in the binder order Rocq records after closing
  the sections (checked with `About` on the Rocq 9.3 reference build).
* Definitions whose source body is a Boolean comparison (`>`, `<=`) are `Bool`
  (`decide …`); propositions built from them use `… = true`.
* `taskset_of Task := {set Task}` is the accepted v0.6 sequence-set
  `Prosa.Util.Seqset.set`.
* The Rocq modules `SporadicTask` and `SporadicTaskset` are nested namespaces;
  `Export SporadicTask` inside `SporadicTaskset` is a Lean `export`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
