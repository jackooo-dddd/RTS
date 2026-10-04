# Report: `classic/analysis/apa/interference_bound_fp.v` (rank 43)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/analysis/apa/interference_bound_fp.v` |
| sha256 | `a248399faf33c7859d8950a04ff4f72304338a07b109c6e19c0ec1b7b4f64f84` |
| Lean module | `Prosa/Classic/Analysis/Apa/InterferenceBoundFp.lean` (namespace `Prosa.Classic.Analysis.Apa.InterferenceBoundFp`) |
| Tier / layer | P / 14 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (1 source → Lean, same names)

- `Definition` `InterferenceBoundFP.total_interference_bound_fp`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Total interference bound for FP scheduling under APA (Rocq module
`InterferenceBoundFP`, `classic/analysis/apa`).

Representation notes: `\sum_((tsk_other, R_other) <- R_prev | P tsk_other) F`
binds the pair by pattern matching in both the filter and the summand and is
`Prosa.Util.Sum.sumFiltered R_prev (fun (tsk_other, _) => P tsk_other)
(fun (tsk_other, R_other) => F)`; the section-local `Let`s
`total_interference_bound` and `hp_task_in alpha'` (which shadows the section
variable `alpha'`) are unfolded.  The Rocq module re-exports
`InterferenceBoundGeneric`.  Binder lists follow the Rocq contract
(`task_deadline` is not taken).

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
