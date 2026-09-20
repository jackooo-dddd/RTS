# Approved Prosa v0.6 Rocq → Lean Representation Policy

## Authority and scope

This policy targets only Prosa v0.6 commit
`414e66760333eaa4ef78c685bcf53291c527a548`. Historical v0.4 Rocq and the
current Lean tree are implementation references, not specifications. A
historical Lean declaration may be reused only after its v0.6 delta is applied,
it is freshly compiled, and semantic correspondence is revalidated.

The authoritative readiness order is `../v06_dependency/file_layers.csv`.
The declaration graph refines local ordering but cannot establish independence
from implicit instances, canonical structures, or HB resolution.

`UNCHANGED_FROM_V04` in the migration table has a deliberately limited
planning meaning: the normalized source declaration command is unchanged under
the available evidence. Since v0.4 has source-command fingerprints but not the
same post-Section `Check @declaration` evidence captured for v0.6, this label
does **not** certify equality of elaborated types or semantics. Every
`REUSE_AFTER_REVALIDATION` row still requires a fresh v0.6 type check and
semantic validation; none of the 144 rows is certified by the migration table.

## General fidelity rule

Translation may change surface syntax but must preserve carrier parameters,
observable computations, constructor cases, class/record fields, and semantic
laws. A theorem proof may be reconstructed independently, but its statement
must correspond to the elaborated v0.6 source statement. Existing v0.4 Lean
code never overrides a changed v0.6 definition.

## `eqType`

`JobType := eqType` and `TaskType := eqType` bundle a carrier and decidable
Boolean equality. The approved Lean representation is a carrier type plus a
`DecidableEq` instance at every boundary at which the Rocq `eqType` is in
scope:

```lean
universe u
abbrev JobType := Type u

variable {Job : JobType} [DecidableEq Job]
```

The evidence is part of every translated declaration boundary whose Rocq
context contains the corresponding `eqType`, including declarations that do
not themselves invoke equality. For example:

```lean
class JobArrival (Job : JobType) [DecidableEq Job] where
  jobArrival : Job → instant

class JobCost (Job : JobType) [DecidableEq Job] where
  jobCost : Job → work

class JobTask
    (Job : JobType) [DecidableEq Job]
    (Task : TaskType) [DecidableEq Task] where
  jobTask : Job → Task
```

This is a representation relation, not an isomorphism between `eqType` and
bare `Type`. The correspondence obligation is:

```text
Rocq boolean equality on related values
↔ Lean equality decided by the selected DecidableEq instance
```

A wrapper structure was considered. It would make ownership of equality
evidence explicit, but causes pervasive carrier projections and makes ordinary
Lean APIs harder to use. `Type + DecidableEq` is therefore preferred, provided
the instance is never silently omitted from translated signatures. The current
Lean aliases `JobType := Type` and `TaskType := Type` are reusable syntax only;
they are not complete translations by themselves.

## `finType`

MathComp `finType` maps to a carrier together with both enumeration and
equality evidence:

```lean
Core : Type w
coreFintype : Fintype Core
coreDecidableEq : DecidableEq Core
```

Both components belong at the same abstraction boundary as the source
`finType`. For `ProcessorState`, they are fields owned by the processor-state
record. Translated derived definitions introduce local instances from those
fields. They must not select an unrelated global enumeration or equality
instance.

Required semantic invariant: the Lean finite enumeration represents exactly
the related Rocq core set, including uniqueness and coverage. No claim that all
of MathComp `finType` is isomorphic to Mathlib `Fintype` is required.

## Sequences and finite sets

The default mappings are deliberately distinct:

| Rocq construct | Lean default | Required semantics |
|---|---|---|
| `seq A` | `List A` | order and multiplicity preserved |
| `{set A}` | `Finset A` | extensional finite membership; no duplicates |
| MathComp `finset` where used extensionally | `Finset A` | membership/extensional equality preserved |

`List` must not be replaced by `Finset` when order or duplicates are
observable. Conversely, an extensional finite set must not be represented by
an arbitrary list unless a uniqueness invariant and extensional equality are
carried explicitly. Conversions require certified membership, duplicate, and
ordering obligations appropriate to the consuming declaration.

## Boolean predicates and propositions

- A source function returning `bool` remains a Lean `Bool` by default.
- MathComp reflected propositions are represented by an explicit bridge such
  as `b = true ↔ P`; reflection is not erased implicitly.
- A source `Prop` maps to Lean `Prop`.
- A Boolean source predicate may be exposed as a Lean `Prop` only at a named
  API boundary with a proved two-way reflection lemma and with downstream
  Boolean computation unaffected.

This policy prevents one file from translating `scheduled_on` as `Bool` while
another silently treats it as an arbitrary proposition. Cross-ITP theorem
validation may additionally require the separately audited Prop/SProp
foundation; that trust boundary is not a representation shortcut.

For the v0.6 Boolean finite existential in `scheduled_in`, the approved
production representation is direct Boolean enumeration:

```lean
def scheduledIn (j : Job) (s : PState.State) : Bool :=
  (Finset.univ : Finset PState.Core).fold Bool.or false fun c =>
    PState.scheduledOn j s c
```

This avoids routing the computation through `decide (∃ ...)`, remains
computable from the owned finite enumeration, and matches MathComp's Boolean
existential truth table. The required reusable reflection lemma is:

```text
scheduledIn PState j s = true
↔ ∃ c : PState.Core, PState.scheduledOn j s c = true
```

The validation-only prototype proves this lemma. Later cross-ITP validation
must additionally relate the Rocq and Lean core enumerations and
`scheduled_on` observations. `supply_in` and `service_in` remain finite sums;
this decision changes neither definition.

## Big operators and intervals

The semantic target for a MathComp natural-number interval sum

```coq
\sum_(m <= i < n) F i
```

is the value of `Finset.sum (Finset.Ico m n) F`, with the half-open interval
`[m,n)`. Required corner cases include `m = n`, `n < m`, and singleton ranges.
The identity is natural-number zero. Filtering preserves the source predicate's
reflection semantics. List folds are acceptable only when enumeration order
does not affect the operation and duplicate-freedom/coverage is established.

`Finset.Ico`, `Finset.range`, or list-fold forms may be chosen for proof
convenience, but they are not interchangeable by syntax. Any alternative form
must be connected to the semantic target by a Lean-kernel-checked definitional
guard or a proved correspondence lemma. Existing finite-sum validation has
already certified the MathComp interval-sum value relation and provides the
preferred reusable bridge.

## Class, record, and inductive declarations

- Preserve all carrier parameters and typeclass parameters.
- Preserve every data field and every law/invariant field.
- Preserve constructor partitioning and pattern-match behavior.
- Derived source definitions remain derived Lean definitions; they must not be
  replaced by unconstrained record fields.
- Moving a carrier from a field to an external parameter is allowed only by an
  explicit bidirectional representation proof and a reviewed impact analysis.

Proof-valued fields may live in `Prop`, but they may not be deleted merely
because Lean can prove them later. Compiler-generated recursors and projections
are not separate translation targets.

## Canonical structures and HB

Canonical-structure or HB machinery is not translated as a collection of
synthetic public declarations. Translate the source-level carrier, mixin,
instance, and observable projections that affect elaborated public types or
computations. Lean instances must be scoped so that they select the same
observable structure; instance synthesis success alone is not evidence of
correspondence. Where the hardened declaration graph reports
`UNRESOLVED_IMPLICIT_DEPENDENCY`, the authoritative file dependencies must be
present before translation and the selected Lean instance must be recorded for
later semantic validation.

## Foundational representation decision: `ProcessorState`

The v0.6 source owns:

```text
State
Core : finType
scheduled_on
supply_on
service_on
service_on_le_supply_on
service_on_implies_scheduled_on
```

and derives `scheduled_in`, `supply_in`, and `service_in`.

### Option A — owned/nested carriers (approved)

```lean
class ProcessorState (Job : Type u) [DecidableEq Job] where
  State : Type v
  Core : Type w
  coreFintype : Fintype Core
  coreDecidableEq : DecidableEq Core
  scheduledOn : Job → State → Core → Bool
  supplyOn : State → Core → Nat
  serviceOn : Job → State → Core → Nat
  serviceOnLeSupplyOn : ∀ j s r, serviceOn j s r ≤ supplyOn s r
  serviceOnImpliesScheduledOn :
    ∀ j s r, scheduledOn j s r = false → serviceOn j s r = 0
```

Derived definitions quantify/sum over the owned `Core` using the owned
instances. This most closely follows the v0.6 abstraction boundary, avoids
unrelated `State` parameters at every downstream declaration, and makes the two
source laws visible to typeclass inference and semantic validation.
`scheduled_in` uses a direct Boolean-or `Finset.univ.fold` (the pinned Mathlib
does not expose `Finset.any`, and its `Finset.toList` is noncomputable); the two
work aggregates use finite sums.

### Option B — external `State` parameter (rejected as the default)

The current Lean tree uses `ProcessorState Job State`, keeps `Core` inside, and
replaces the per-core supply/service interface with aggregate `service_in`.
Although convenient for the v0.4 source, it no longer matches v0.6: it causes
parameter proliferation, removes `supply_on`/`service_on`, and cannot derive
the required finite sums or per-core laws.

### Decision

Use Option A. A validation-only prototype compiles under Lean 4.33.1 and
Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`. Existing current-Lean
processor code is reference/adaptation material only. `ProcessorState` and its
service chain must be translated as one reviewed foundation slice before
downstream schedule/model files are considered ready.

## Policy compliance

Every future translation change should record the relevant policy identifier
from `v06_migration_table.csv`. Deviations require a documented representation
relation and review; individual files must not invent alternate mappings.
