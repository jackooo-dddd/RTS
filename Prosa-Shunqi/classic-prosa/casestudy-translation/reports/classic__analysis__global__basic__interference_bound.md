# Report: `classic/analysis/global/basic/interference_bound.v` (rank 40)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/analysis/global/basic/interference_bound.v` |
| sha256 | `5fc1a41a8fb23ad6a85c7f0f00057a37d13618942cf8fc42cdc19022875d91f0` |
| Lean module | `Prosa/Classic/Analysis/Global/Basic/InterferenceBound.lean` (namespace `Prosa.Classic.Analysis.Global.Basic.InterferenceBound`) |
| Tier / layer | P / 13 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (1 source → Lean, same names)

- `Definition` `InterferenceBoundGeneric.interference_bound_generic`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Bertogna and Cirinei's generic interference bound (Rocq module
`InterferenceBoundGeneric`).

Representation notes: the section-local `Let task_with_response_time` is
`sporadic_task × time`, and `Let tsk_other := fst tsk_R`, `Let R_other := snd tsk_R`
are unfolded to `tsk_R.1` / `tsk_R.2`; `minn` is `min`.  Binder lists follow the
Rocq contract: the section variables `task_deadline` and `R_prev` are not
used by the definition, so it does not take them.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
