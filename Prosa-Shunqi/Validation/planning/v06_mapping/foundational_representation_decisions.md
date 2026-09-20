# Foundational Representation Decisions

Authority: Prosa v0.6 commit
`414e66760333eaa4ef78c685bcf53291c527a548`. Fan-out and layer information is
from the hardened v0.6 dependency artifacts, not from the current Lean tree.

## Decisions

| v0.6 declaration | v0.4 evolution | Current Lean candidate | Decision |
|---|---|---|---|
| `instant`, `duration`, `work` | source command unchanged | strong v0.4 candidate | use `Nat`; reuse only after fresh v0.6 type/semantic validation |
| `JobType`, `TaskType` | source command unchanged (`eqType`) | bare `Type` aliases | adapt to the approved carrier + `DecidableEq` boundary |
| `JobArrival`, `JobCost`, `JobTask` | source command structurally unchanged | strong v0.4 candidates | retain fields and carry all corresponding `DecidableEq` parameters; revalidate |
| `ProcessorState` | substantively evolved | old v0.4-shaped class | adopt nested `State/Core`, per-core operations, and both laws |
| `scheduled_in` | v0.4 class field externalized as a v0.6 derived definition | extracted Lean definition | adapt after new `ProcessorState`; keep Boolean finite existential |
| `supply_in` | new in v0.6 | none | new translation as sum over all cores |
| `service_in` | old arbitrary aggregate field replaced by a derived per-core sum | old aggregate field | reference only; translate the v0.6 sum anew |
| `service_at`, `service_during`, `service`, `completed_by` | source text mostly stable, but the service dependency changed | strong v0.4 candidates | adapt/revalidate as a dependency-sensitive chain |
| `completes_at` | computational definition changed, including the zero-time case | faithful v0.4 candidate, known v0.6 mismatch | adapt to exact v0.6 definition; do not reuse unchanged |
| `arrivals_at`, `arrivals_between` | unchanged | strong v0.4 candidates | retain `List`/sequence order and multiplicity; revalidate |

## Equality-bearing carriers

In this planning data, “unchanged” means only that the normalized source
declaration command is unchanged. v0.4 lacks matching elaborated
`Check @declaration` evidence, so no row is certified as elaborated-type or
semantically unchanged. The 144 `REUSE_AFTER_REVALIDATION` rows remain future
validation obligations.

`JobType` has 1,403 and `TaskType` 774 extracted transitive declaration
dependents. The approved representation is `Type u` plus `DecidableEq` at the
same semantic boundary. Equality behavior is an explicit correspondence
obligation. The old bare aliases alone are insufficient evidence, so both rows
are `ADAPT_OLD_LEAN`, not automatic reuse.

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

This is intentionally incompatible with blindly retaining the current
v0.4-shaped `ProcessorState Job State`. The old class can guide names and
concrete processor adaptations but cannot serve as the v0.6 implementation.

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

The representation choices above are fixed for translation-pipeline
preparation. Rows classified `UNCLEAR` in the migration table remain
`REVIEW_REQUIRED` because their historical counterpart is ambiguous, not
because these foundational policies are undecided. CoqEAL refinement rows are
deferred pending external elaboration evidence.
