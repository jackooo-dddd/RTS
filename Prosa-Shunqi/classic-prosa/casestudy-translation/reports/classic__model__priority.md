# Report: `classic/model/priority.v` (rank 26)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/priority.v` |
| sha256 | `e31466a2edede2cfd7f3f5ac9a97792fca3e720f17342b1a8475c97a289cd134` |
| Lean module | `Prosa/Classic/Model/Priority.lean` (namespace `Prosa.Classic.Model.Priority`) |
| Tier / layer | S / 9 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (35 source → Lean, same names)

- `Definition` `Priority.FP_policy`
- `Definition` `Priority.JLFP_policy`
- `Definition` `Priority.JLDP_policy`
- `Definition` `Priority.FP_to_JLFP`
- `Definition` `Priority.FP_to_JLDP`
- `Definition` `Priority.JLFP_to_JLDP`
- `Definition` `Priority.FP_is_reflexive`
- `Definition` `Priority.FP_is_irreflexive`
- `Definition` `Priority.FP_is_transitive`
- `Definition` `Priority.FP_is_total_over_task_set`
- `Definition` `Priority.FP_is_antisymmetric_over_task_set`
- `Definition` `Priority.JLFP_is_reflexive`
- `Definition` `Priority.JLFP_is_irreflexive`
- `Definition` `Priority.JLFP_is_transitive`
- `Definition` `Priority.JLFP_is_total`
- `Definition` `Priority.JLFP_respects_sequential_jobs`
- `Definition` `Priority.JLDP_is_reflexive`
- `Definition` `Priority.JLDP_is_irreflexive`
- `Definition` `Priority.JLDP_is_transitive`
- `Definition` `Priority.JLDP_is_total`
- `Definition` `Priority.RM`
- `Definition` `Priority.DM`
- `Lemma` `Priority.RM_is_reflexive`
- `Lemma` `Priority.RM_is_transitive`
- `Lemma` `Priority.DM_is_reflexive`
- `Lemma` `Priority.DM_is_transitive`
- `Lemma` `Priority.any_reflexive_FP_respects_sequential_jobs`
- `Definition` `Priority.EDF`
- `Lemma` `Priority.EDF_is_reflexive`
- `Lemma` `Priority.EDF_is_transitive`
- `Lemma` `Priority.EDF_is_total`
- `Definition` `Priority.job_relative_dealine`
- `Lemma` `Priority.EDF_respects_sequential_jobs`
- `Definition` `Priority.higher_priority_task`
- `Definition` `Priority.different_task`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Priority policies (Rocq module `Priority`).

Representation notes:
* `rel T` is `T → T → Bool`; MathComp's relation properties are kept with their
  binder order: `reflexive R := ∀ x, R x x`, `irreflexive R := ∀ x, R x x = false`,
  `transitive R := ∀ y x z, R x y → R y z → R x z` (Boolean results `= true`).
* Boolean comparisons are `Bool` (`decide …`); `a == b` is `decide (a = b)` and
  `a != b` is `!decide (a = b)`.
* Binder lists follow the Rocq contract, e.g.
  `any_reflexive_FP_respects_sequential_jobs {Job Task} job_arrival job_task …`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
