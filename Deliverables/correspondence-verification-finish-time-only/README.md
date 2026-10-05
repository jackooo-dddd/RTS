# Correspondence verification: Prosa v0.6 (Rocq) ↔ Lean 4

For each Prosa v0.6 source file, this folder shows the official Rocq file, its Lean 4 translation, each declaration printed in full
side by side, and the Rocq certificates proving that they correspond, together with the assumptions those certificates
use.

So far it covers one file: [`analysis/definitions/finish_time.v`](files/analysis/definitions/finish_time/README.md).

## How correspondence is shown

The compiled Lean declarations are imported into Rocq. For each public declaration, a Rocq certificate relates the
official Prosa declaration to the imported Lean one:
- **definitions:** related inputs give related outputs. For example, natural numbers are related by `SubNatRel`;
- **lemmas and theorems:** the two statements are logically equivalent (`PropSPropRel`).

## Layout

```text
correspondence-verification/
├── shared/                     modules used by several files: certificates and Lean interfaces (see shared/README.md)
└── files/<v0.6 source path>/   one folder per Prosa v0.6 source file
```

Each file's folder contains:

| Folder | Contents |
|---|---|
| `README.md` | The file's declarations with their certificates, its own certificate modules, and the assumptions |
| `1_source_rocq/` | The official `.v` file and its Rocq 9.3 compatibility patch, which changes proof scripts only |
| `2_translation_lean/` | The Lean translation |
| `3_printed_declarations/` | One page per declaration, printed in full (see below) |
| `4_correspondence/` | The file's own certificates; `shared.md` lists the shared modules they use |
| `5_assumptions/` | `assumption_summary.json`: the audited assumptions of each certificate |

## Printed declarations

Each page shows the declaration three ways, each with its type and, for definitions, its body:

| Section | Printed with |
|---|---|
| **Official Rocq** | `About`, `Check @` and `Print`, with `Set Printing Implicit` and `Set Printing Coercions`, so every implicit argument and coercion is shown |
| **Lean** | `#check @` (all binders, including instance arguments) and `#print` |
| **Lean, imported into Rocq** | `Check @` and `Print` on the imported constant, with the same Rocq settings. Lean's auto-generated instance binder names (`inst____at___…__hygCtx__hygN`) are shortened to `inst_N`. |

## Assumptions

Each file's README lists, by category, what `Print Assumptions` reports for its certificates:

| Category | What it is |
|---|---|
| Prop/SProp foundation (`interpret_strict`) | The bridge between Lean propositions, imported as Rocq `SProp`, and Rocq `Prop`. **The only axiom the comparison adds.** |
| Imported Lean axioms (`propext`, `Quot_sound`, `Classical_choice`) | Copies of Lean's three standard axioms, present because the certificates refer to imported Lean terms that depend on them |
| Definitional UIP (`eq`, `True`, `HEq`, `SvcTrue`, …) | Not an axiom. These are Lean's equality and a few always-true propositions, imported into Rocq. Rocq lets them be used for rewriting only under its *definitional UIP* setting: any two proofs of the same equality count as identical, which is the rule Lean's kernel already uses. |
| Rocq primitives (`PrimInt63.*`) | Rocq built-in primitive integers used by the importer; not axioms |

Every certificate is also checked to have no semantic premises, no statement-only dependencies and no use of the
file's own theorems.
