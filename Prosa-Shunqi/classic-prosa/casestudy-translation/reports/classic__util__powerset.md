# Report: `classic/util/powerset.v` (rank 12)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/powerset.v` |
| sha256 | `b5f49e66830ee5b3f5026f1ffc3ba97a718f1736dd48e8f4de6d7d497c38fdc7` |
| Lean module | `Prosa/Classic/Util/Powerset.lean` (namespace `Prosa.Classic.Util.Powerset`) |
| Tier / layer | S / 2 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (2 source → Lean, same names)

- `Definition` `powerset`
- `Lemma` `mem_powerset`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `mask_subset`.

## Representation notes

The power set of a sequence.

Representation notes:
* `powerset l` maps MathComp's `mask m l` over `enum {: (size l).-tuple bool}`.  The
  Lean helpers below reproduce both exactly: `mask` is MathComp's `mask` (same
  recursion), and `boolTupleEnum n` is the MathComp enumeration of `n.-tuple bool`
  (`FinTuple.enum`: `iter n extend [:: [::]]` with `extend e := flatten (codom (fun x
  => map (cons x) e))`, and `enum bool = [:: true; false]`), so the list order is the
  source order.
* `{subset y <= x}` is `∀ z, z ∈ y → z ∈ x`; `y \in powerset x` in proposition position
  is `y ∈ powerset x`.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
