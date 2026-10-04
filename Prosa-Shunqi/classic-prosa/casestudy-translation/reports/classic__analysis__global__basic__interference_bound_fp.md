# Report: `classic/analysis/global/basic/interference_bound_fp.v` (rank 44)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/analysis/global/basic/interference_bound_fp.v` |
| sha256 | `5c4c6e505fd479f105a5332ea95140cd819e23e64293afcc6b86d3808b5239f0` |
| Lean module | `Prosa/Classic/Analysis/Global/Basic/InterferenceBoundFp.lean` (namespace `Prosa.Classic.Analysis.Global.Basic.InterferenceBoundFp`) |
| Tier / layer | P / 14 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (1 source → Lean, same names)

- `Definition` `InterferenceBoundFP.total_interference_bound_fp`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Total interference bound for FP scheduling (Rocq module `InterferenceBoundFP`).

Representation notes: `\sum_((tsk_other, R_other) <- R_prev) F` binds the pair by
pattern matching and is `Prosa.Util.Sum.sumSeq R_prev (fun (tsk_other, R_other) => F)`;
the section-local `Let total_interference_bound` is unfolded.  The Rocq module
re-exports `InterferenceBoundGeneric`.  Binder lists follow the Rocq contract:
`total_interference_bound_fp` does not take the unused section variables
`task_deadline` and `higher_eq_priority`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
