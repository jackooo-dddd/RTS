# `util/tactics.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `neqP` | Lemma | `Prosa.Util.Tactics.neqP` | `neqP_statement_correspondence_certificate` | [view](3_printed_declarations/neqP.md) |
| `modusponens` | Lemma | `Prosa.Util.Tactics.modusponens` | `modusponens_statement_certificate` | [view](3_printed_declarations/modusponens.md) |

## Certificates

| Module | Role |
|---|---|
| [`TacticsCertificate`](4_correspondence/TacticsCertificate.v) | Structural logical-relation proof for the exact polymorphic logical shell of the official and imported `modusponens` theorem types. |
| [`TacticsClosureCertificate`](4_correspondence/TacticsClosureCertificate.v) | Exact-type guards are separate from the correspondence certificate, so the latter has no source- or target-theorem self dependency. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | — |
| Imported Lean axioms | — |
| Definitional UIP | `EqValidationTrue`, `eq` |
| Rocq primitives | — |
