# Report: `classic/model/schedule/apa/affinity.v` (rank 29)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/model/schedule/apa/affinity.v` |
| sha256 | `03953e413747cfb05cc68cf4d066af456632601fef5df6cb7befb780cc2932f4` |
| Lean module | `Prosa/Classic/Model/Schedule/Apa/Affinity.lean` (namespace `Prosa.Classic.Model.Schedule.Apa.Affinity`) |
| Tier / layer | S / 10 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (7 source → Lean, same names)

- `Definition` `Affinity.affinity`
- `Definition` `Affinity.task_affinity`
- `Definition` `Affinity.can_execute_on`
- `Definition` `Affinity.task_scheduled_on_affinity`
- `Definition` `Affinity.is_subaffinity`
- `Lemma` `Affinity.leq_subaffinity`
- `Definition` `Affinity.affinity_intersects`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): none.

## Representation notes

Processor affinities (Rocq module `Affinity`).

Representation notes: an affinity `{set (processor num_cpus)}` is the accepted
v0.6 sequence-set `Prosa.Util.Seqset.set (Fin num_cpus)`; `cpu \in alpha` is
`decide (cpu ∈ alpha)`; `{subset A <= B}` is `∀ x, x ∈ A → x ∈ B`; `#|A|` is
`(Finset.univ.filter (· ∈ A)).card` (as in classic `Seqset`); the Boolean
quantifier `[exists cpu, P cpu]` is `(List.finRange num_cpus).any P`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
