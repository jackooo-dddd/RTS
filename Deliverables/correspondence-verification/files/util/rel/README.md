# `util/rel.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `monotone` | Definition | `Prosa.Util.Rel.monotone` | `monotone_correspondence_certificate` | [view](3_printed_declarations/monotone.md) |
| `total_over_list` | Definition | `Prosa.Util.Rel.total_over_list` | `total_over_list_correspondence_certificate` | [view](3_printed_declarations/total_over_list.md) |
| `antisymmetric_over_list` | Definition | `Prosa.Util.Rel.antisymmetric_over_list` | `antisymmetric_over_list_correspondence_certificate` | [view](3_printed_declarations/antisymmetric_over_list.md) |

## Certificates

| Module | Role |
|---|---|
| [`RelClosureCertificate`](4_correspondence/RelClosureCertificate.v) | Proves or defines `RelPointwise`, `rel_or_forward`, `rel_or_backward_strict` and 2 more. |
| [`RelCertificate`](4_correspondence/RelCertificate.v) | Parametric correspondence for a higher-order Boolean relation. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `RelValidationTrue`, `eq` |
| Rocq primitives | — |
