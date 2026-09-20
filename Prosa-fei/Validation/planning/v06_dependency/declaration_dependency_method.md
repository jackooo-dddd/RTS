# Declaration Dependency Extraction Method

## Status

```text
FILE_DAG_STATUS = VERIFIED_COMPLETE_FOR_PINNED_SOURCE
DECLARATION_DAG_STATUS =
VERIFIED_EXPLICIT_TRANSLATION_RELEVANT_DEPENDENCIES
WITH_DOCUMENTED_IMPLICIT/GENERATED LIMITATIONS
```

The file graph remains the authoritative translation-readiness graph. The declaration graph is a fine-grained scheduling and context aid; it must not be used as the sole criterion that a declaration's environment is ready.

## Evidence classes

- `EXPLICIT_GLOB_DEPENDENCY`: a Rocq `.glob` reference location lies inside the source declaration's final type command or included computational body span.
- `ELABORATED_TYPE_CONFIRMED`: the dependent declaration's actual post-Section-closure type was resolved and printed by Rocq `Check @qualified.name`. This confirms the final type, not that every dependency edge was recovered.
- `GENERATED_SYMBOL_MAPPED`: a reference to a constructor/projection/HB-generated symbol was mapped to a public source owner without adding the generated symbol to the public inventory.
- `UNRESOLVED_IMPLICIT_DEPENDENCY`: `.glob` does not provide a completeness theorem for implicit typeclass search, canonical structures, or HB resolution. No missing edge is guessed.

## Actual extraction totals

- Public source declarations: **2439**.
- Direct declaration edges: **4628**.
- Generated-symbol mappings: **93**.
- Edges using a generated-symbol mapping: **734**.
- Generated/local symbols referenced but not unambiguously mapped: **71**.
- Confidence distribution: `{'EXPLICIT_ONLY': 1589, 'HIGH_EXPLICIT_AND_GENERATED': 611, 'UNRESOLVED_EXTERNAL': 239}`.
- Edge evidence occurrences: `{'EXPLICIT_GLOB_DEPENDENCY': 3916, 'ELABORATED_TYPE_CONFIRMED': 3263, 'GENERATED_SYMBOL_MAPPED': 734}`.
- Mapping methods: `{'SOURCE_DECLARATION_SPAN': 80, 'HB_SAME_COMMAND_UNIQUE_STRUCTURAL_OWNER': 13}`.
- Unresolved generated/local kinds: `{'prf': 37, 'inst': 32, 'def': 2}`.

## Generated symbols

Constructors and projections are mapped by a byte-accurate source span shared with their owner `Inductive`, `Record`, `Structure`, or `Class`. HB symbols are mapped only when the same `HB.instance Definition _` command explicitly references exactly one public structural owner. Ambiguous cases remain unresolved. Compiler-generated symbols never become public inventory nodes.

## `Definition ... Proof ... Defined` audit

The pinned tree contains **1** computational declaration(s) ending in `Defined.`.

| File | Line | Kind | Name | Public named node | Body refs |
|---|---:|---|---|---|---:|
| `util/setoid.v` | 53 | Instance | `<anonymous>` | False | 0 |

At v0.6 the sole occurrence is the anonymous global `RewriteRelation le` instance in `util/setoid.v`. It has no proof-body references between its header and `Defined.` and is not a named public declaration node. Therefore the previous named-public DAG missed no computational body edge from this pattern. Its possible participation in later instance search remains covered by `UNRESOLVED_IMPLICIT_DEPENDENCY`.

For a named `Definition`/`Fixpoint`/`CoFixpoint`/`Instance` ending in `Defined.`, the extractor now extends the body span through `Defined.`. Opaque `Qed.` proof bodies and all theorem/lemma proof bodies remain excluded.

## Implicit resolution limitation

Spot inspection shows that `.glob` records many selected `inst` references and all source-located projection/constructor references, but it does not establish that every elaborator-inserted typeclass, canonical-structure, coercion, or HB dependency has a recoverable source location. In particular, 71 referenced local/generated symbols have no unambiguous public owner (mostly local proof constants and local instances). The graph records them but does not invent edges.

## Scheduling rule

Use `file_layers.csv` as the mandatory readiness order. Use `declaration_layers.csv` only to order work within an already-ready file/dependency context. Absence of a declaration edge is not evidence of semantic independence.
