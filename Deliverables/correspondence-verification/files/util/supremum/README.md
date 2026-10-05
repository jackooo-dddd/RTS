# `util/supremum.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `choose_superior` | Definition | `Prosa.Util.Supremum.choose_superior` | `choose_superior_correspondence_certificate` | [view](3_printed_declarations/choose_superior.md) |
| `supremum` | Definition | `Prosa.Util.Supremum.supremum` | `supremum_correspondence_certificate` | [view](3_printed_declarations/supremum.md) |
| `supremum_unfold` | Lemma | `Prosa.Util.Supremum.supremum_unfold` | `supremum_unfold_statement_correspondence_certificate` | [view](3_printed_declarations/supremum_unfold.md) |
| `supremum_exists` | Lemma | `Prosa.Util.Supremum.supremum_exists` | `supremum_exists_statement_correspondence_certificate` | [view](3_printed_declarations/supremum_exists.md) |
| `supremum_none` | Lemma | `Prosa.Util.Supremum.supremum_none` | `supremum_none_statement_correspondence_certificate` | [view](3_printed_declarations/supremum_none.md) |
| `supremum_in` | Lemma | `Prosa.Util.Supremum.supremum_in` | `supremum_in_statement_correspondence_certificate` | [view](3_printed_declarations/supremum_in.md) |
| `supremum_spec` | Lemma | `Prosa.Util.Supremum.supremum_spec` | `supremum_spec_statement_correspondence_certificate` | [view](3_printed_declarations/supremum_spec.md) |

## Certificates

| Module | Role |
|---|---|
| [`SupremumClosureCertificate`](4_correspondence/SupremumClosureCertificate.v) | Exact theorem-type guards. |
| [`SupremumCertificate`](4_correspondence/SupremumCertificate.v) | Proves or defines `SupBoolRel`, `choose_superior_correspondence_certificate`, `supremum_correspondence_certificate`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `SupTheoremTrue`, `SupValidationTrue`, `eq` |
| Rocq primitives | — |
