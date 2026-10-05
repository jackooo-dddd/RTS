# `util/setoid.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `leb` | Inductive | `Prosa.Util.Setoid.leb` | `leb_constructor_correspondence_certificate` | [view](3_printed_declarations/leb.md) |
| `leb_eq` | Lemma | `Prosa.Util.Setoid.leb_eq` | `leb_eq_statement_certificate` | [view](3_printed_declarations/leb_eq.md) |
| `leqRW` | Definition | `Prosa.Util.Setoid.leqRW` | `leqRW_definition_type_certificate` | [view](3_printed_declarations/leqRW.md) |

## Certificates

| Module | Role |
|---|---|
| [`SetoidCertificate`](4_correspondence/SetoidCertificate.v) | Exact semantic statement exposed by the source theorem. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `StTrue`, `SubNatTrue`, `eq` |
| Rocq primitives | — |
