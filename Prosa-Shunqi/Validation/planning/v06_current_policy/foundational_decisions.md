# Foundational Representation Decisions

Authority: Prosa v0.6 commit
`414e66760333eaa4ef78c685bcf53291c527a548`. Fan-out and layer information is
from the hardened v0.6 dependency artifacts, not from the current Lean tree.

## Decisions

| v0.6 declaration | Approved representation / obligation |
|---|---|
| `instant`, `duration`, `work` | use `Nat`; validate each actual compiled alias against v0.6 |
| `JobType`, `TaskType` | carrier plus `DecidableEq` at each source equality boundary |
| `JobArrival`, `JobCost`, `JobTask` | preserve every field and corresponding equality-evidence parameter |
| `ProcessorState` | own `State/Core`, per-core operations, and both laws |
| `scheduled_in` | derived Boolean finite existential over the owned cores |
| `supply_in`, `service_in` | derived finite sums of the corresponding per-core operations |
| `service_at`, `service_during`, `service`, `completed_by` | validate the complete dependency chain compositionally |
| `completes_at` | preserve the exact v0.6 zero-time behavior |
| `arrivals_at`, `arrivals_between` | retain sequence order and multiplicity |

## Equality-bearing carriers

`JobType` has 1,403 and `TaskType` 774 extracted transitive declaration
dependents. The approved representation is `Type u` plus `DecidableEq` at the
same semantic boundary. Equality behavior is an explicit correspondence
obligation; a bare carrier alias alone is insufficient.

The same equality evidence is retained even by a class whose own field does
not compare values: `JobArrival` and `JobCost` carry `[DecidableEq Job]`, and
`JobTask` carries both `[DecidableEq Job]` and `[DecidableEq Task]`. This keeps
the Lean boundary consistent with the source `eqType` binders.

## Processor state and finite cores

The v0.6 `ProcessorState` owns `State`, `Core : finType`, three observable
per-core operations, and two laws. The approved Lean record owns `State`,
`Core`, `Fintype Core`, `DecidableEq Core`, matching operations, and matching
laws. `scheduled_in`, `supply_in`, and `service_in` remain outside the class as
derived definitions. `scheduled_in` is a computable Boolean-or fold over
`Finset.univ` (the pinned Mathlib has no `Finset.any`, and `Finset.toList` is
noncomputable); its prototype proof establishes that it is true exactly when
some core's `scheduled_on` Boolean is true. The other two definitions remain
finite sums.

An external `State` parameter or aggregate-only service field does not
represent the complete approved v0.6 interface.

## Sequence, finite-set, and big-operator boundaries

- Arrival sequences retain ordered `List` semantics, including duplicates
  until a separate uniqueness property is assumed.
- Extensional finite sets use `Finset` and require `DecidableEq`.
- MathComp interval sums use half-open `Finset.Ico`; empty and reversed ranges
  produce the additive identity.
- A proof-oriented `range`, list fold, or normalization is allowed only behind
  a checked equality/correspondence guard.

## Boolean reflection

Computational Boolean predicates such as `scheduled_on` stay `Bool`. Their
truth interpretation is `b = true`, with explicit reflection lemmas when a
Lean `Prop` consumer is required. Source laws stated through Boolean negation
must preserve the same truth table rather than being casually rewritten to an
unrelated proposition. In particular, `scheduled_in` does not use a
Prop-mediated `decide`; it performs direct Boolean enumeration and exposes a
proved existential-reflection lemma for later semantic validation.

## Review state

The representation choices above are fixed for current translation work.
CoqEAL refinement declarations remain deferred pending external elaboration
evidence; any new representation ambiguity requires an explicit review.
