# `util/seqset.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `set` | Record | `Prosa.Util.Seqset.set` | `seqset_set_correspondence_certificate` | [view](3_printed_declarations/set.md) |
| `set_of` | Definition | `Prosa.Util.Seqset.set_of` | `seqset_set_of_correspondence_certificate` | [view](3_printed_declarations/set_of.md) |
| `set_uniq` | Lemma | `Prosa.Util.Seqset.set_uniq` | `seqset_set_uniq_statement_correspondence_certificate` | [view](3_printed_declarations/set_uniq.md) |

## Certificates

| Module | Role |
|---|---|
| [`SeqsetClosureCertificate`](4_correspondence/SeqsetClosureCertificate.v) | `set_of` only discharges the source phantom and target instance parameters. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `SeqsetTrue`, `eq` |
| Rocq primitives | — |
