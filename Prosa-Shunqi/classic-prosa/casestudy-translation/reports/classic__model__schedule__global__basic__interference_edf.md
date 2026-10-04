# Report: `classic/model/schedule/global/basic/interference_edf.v` (rank 45)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/global/basic/interference_edf.v` |
| sha256 | `f79473b69ddc340fc3643ef30026a064914f9507696ccef438c2f7913a1dc8eb` |
| Lean module | `Prosa/Classic/Model/Schedule/Global/Basic/InterferenceEdf.lean` (namespace `Prosa.Classic.Model.Schedule.Global.Basic.InterferenceEdf`) |
| Tier / layer | P / 14 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (1 source → Lean, same names)

- `Lemma` `InterferenceEDF.interference_under_edf_implies_shorter_deadlines`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Interference under EDF in global schedules (Rocq module `InterferenceEDF`).

Representation notes: `x != 0` in proposition position is `(!decide (x = 0)) = true`.
Binder lists follow the Rocq contract (`arr_seq` is implicit and `num_cpus` is an
explicit section `Variable` here).

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
