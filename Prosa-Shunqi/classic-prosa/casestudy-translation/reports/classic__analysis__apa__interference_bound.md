# Report: `classic/analysis/apa/interference_bound.v` (rank 39)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/analysis/apa/interference_bound.v` |
| sha256 | `81571d1c6ceae2cd4e870d893758b569f39a08877561ecbfb5882780c7494347` |
| Lean module | `Prosa/Classic/Analysis/Apa/InterferenceBound.lean` (namespace `Prosa.Classic.Analysis.Apa.InterferenceBound`) |
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
Rocq contract: the section variables `task_deadline` and `R_prev` (and, in this APA file, `num_cpus`) are not
used by the definition, so it does not take them.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
