# `util/superadditivity.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `superadditive_at` | Definition | `Prosa.Util.Superadditivity.superadditive_at` | `superadditive_at_correspondence` | [view](3_printed_declarations/superadditive_at.md) |
| `superadditive_until` | Definition | `Prosa.Util.Superadditivity.superadditive_until` | `superadditive_until_correspondence` | [view](3_printed_declarations/superadditive_until.md) |
| `superadditive` | Definition | `Prosa.Util.Superadditivity.superadditive` | `superadditive_correspondence` | [view](3_printed_declarations/superadditive.md) |
| `superadditive_standard` | Definition | `Prosa.Util.Superadditivity.superadditive_standard` | `superadditive_standard_correspondence` | [view](3_printed_declarations/superadditive_standard.md) |
| `superadditive_standard_equivalence` | Lemma | `Prosa.Util.Superadditivity.superadditive_standard_equivalence` | `superadditivity_equivalence_statement_certificate` | [view](3_printed_declarations/superadditive_standard_equivalence.md) |
| `superadditive_first_zero` | Lemma | `Prosa.Util.Superadditivity.superadditive_first_zero` | `superadditivity_first_zero_statement_certificate` | [view](3_printed_declarations/superadditive_first_zero.md) |
| `superadditive_monotone` | Lemma | `Prosa.Util.Superadditivity.superadditive_monotone` | `superadditivity_monotone_statement_certificate` | [view](3_printed_declarations/superadditive_monotone.md) |
| `superadditive_leq_mul` | Lemma | `Prosa.Util.Superadditivity.superadditive_leq_mul` | `superadditivity_leq_mul_statement_certificate` | [view](3_printed_declarations/superadditive_leq_mul.md) |
| `superadditive_unbounded` | Lemma | `Prosa.Util.Superadditivity.superadditive_unbounded` | `superadditivity_unbounded_statement_certificate` | [view](3_printed_declarations/superadditive_unbounded.md) |
| `minimal_superadditive_extension` | Definition | `Prosa.Util.Superadditivity.minimal_superadditive_extension` | `sa_minimal_extension_related` | [view](3_printed_declarations/minimal_superadditive_extension.md) |
| `minimal_extension_superadditive_at_horizon` | Theorem | `Prosa.Util.Superadditivity.minimal_extension_superadditive_at_horizon` | `sa_horizon_at_statement_certificate` | [view](3_printed_declarations/minimal_extension_superadditive_at_horizon.md) |
| `minimal_extension_superadditive_until` | Lemma | `Prosa.Util.Superadditivity.minimal_extension_superadditive_until` | `sa_horizon_until_statement_certificate` | [view](3_printed_declarations/minimal_extension_superadditive_until.md) |

## Certificates

| Module | Role |
|---|---|
| [`SuperadditivitySourceBindingAudit`](4_correspondence/SuperadditivitySourceBindingAudit.v) | Kernel conversion guards bind each proof-facing extracted source slice to the combined twelve-declaration slice used for publication. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `HEq_inst1`, `SubNatTrue`, `SuperadditivityTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
